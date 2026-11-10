"""지피티 독립 사실 검수 (읽기 전용).

시트 '검수' 탭에서 검수 요청 행(E·H열이 비어 있는 행)을 읽고, D열의 항목마다 근거 URL 페이지를
코드가 직접 받아 와서 모델에게 대조시킨다. 결과는 JSON 파일로만 남긴다(drafts 브랜치 review/ 폴더).
- 시트·허브·승인·영상 제작은 건드리지 않는다. 판정(verdict)은 참고값이며 최종 판정은 Claude가 checks로 다시 계산한다.
- 인용문 존재 여부(코드가 원문에서 직접 확인)와 주장 뒷받침 여부(모델이 인용문과 주장의 관계를 따로 평가)를 구분한다.
  둘 다 통과해야 일치/불일치로 인정하고, 하나라도 부족하면 보류한다.
- 페이지 접근 실패·본문 부족·차단된 주소는 모델에게 묻지 않고 보류.
- 출처 URL은 https만 허용하고, 내부·사설 주소와 리다이렉션 도착지까지 막는다(SSRF 방지).

사용:
  python gpt_review.py run --out review                         # 검수 실행 (OPENAI_API_KEY 필요)
  python gpt_review.py verify --json 결과.json --ctx 맥락.json   # Claude 반영 전 검증(JSON 1개)
  python gpt_review.py select --ctx 맥락.json --json a.json b.json   # 후보 여러 개 중 현재 요청과 맞는 1개 선택
"""
import os, sys, re, io, csv, json, time, html, socket, ssl, ipaddress, hashlib, argparse
import http.client, urllib.parse, urllib.request
from decimal import Decimal, InvalidOperation
from datetime import datetime, timezone, timedelta

SHEET_ID = os.environ.get("REVIEW_SHEET_ID", "1K8z8h5uNxAxj92Zy2wbv5qonpRJqtn23ekMRA0A-6cc")
MODEL = os.environ.get("GPT_MODEL", "gpt-4.1")
KST = timezone(timedelta(hours=9))
MAX_AGE_H = 35          # Claude의 36시간 지연 규칙보다 짧게: 제출 후 35시간이 지난 미검수 행은 검수하지 않음
MIN_PAGE_CHARS = 400    # 이보다 짧으면 JS 렌더링·유료 벽 등으로 보고 보류
MAX_PAGE_CHARS = 45000
MAX_BYTES = 2_000_000
MAX_REDIRECTS = 5
SCHEMA_VERSION = 1
SUPPORTED_SCHEMAS = (1,)
RESULTS = ("일치", "불일치", "보류")
SCRIPT_COLS = 14        # A:N


# ---------- 공통 ----------
def norm(s):
    s = (s or "").replace("\r\n", "\n").replace("\r", "\n")
    return "\n".join(line.rstrip() for line in s.split("\n")).strip()


def fold(s):
    """인용문 대조용 정규화: 공백·따옴표·대시·대소문자 차이를 무시."""
    s = html.unescape(s or "")
    s = s.replace(" ", " ").replace("​", "")
    s = re.sub(r"[‘’‚′]", "'", s)
    s = re.sub(r"[“”„″]", '"', s)
    s = re.sub(r"[‐-―−]", "-", s)
    return re.sub(r"\s+", " ", s).strip().lower()


def parse_iso(s):
    try:
        d = datetime.fromisoformat((s or "").strip().replace("Z", "+00:00"))
    except Exception:
        return None
    return d if d.tzinfo else None


def now_kst():
    return datetime.now(KST).replace(microsecond=0).isoformat()


def parse_range(rng):
    m = re.fullmatch(r"\s*'?Untitled'?!A(\d+):N(\d+)\s*", rng or "")
    if not m:
        return None
    a, b = int(m.group(1)), int(m.group(2))
    return (a, b) if 1 < a <= b else None


TAIL_RE = re.compile(r"\s*\(근거:.*\)\s*$")
ITEM_RE = re.compile(r"^\s*(\d+)\.\s*(.+?)\s*\|\|\s*(\S+)\s*(\(근거:.*\))?\s*$")


def strip_tail(s):
    return TAIL_RE.sub("", s or "").strip()


def parse_items(d_text):
    """D열 -> [(번호, 사실 한 줄, URL)]. Claude의 '(근거: …)' 꼬리는 버린다(독립 검수). 형식이 틀리면 ValueError."""
    items = []
    for line in norm(d_text).split("\n"):
        if not line.strip():
            continue
        m = ITEM_RE.match(line)
        if not m:
            raise ValueError("검수 요청 항목 형식 오류: " + line[:60])
        items.append((int(m.group(1)), m.group(2).strip(), m.group(3)))
    nums = [n for n, _, _ in items]
    if not items or nums != list(range(1, len(items) + 1)):
        raise ValueError("항목 번호가 1부터 연속이 아님: %s" % nums)
    return items


# ---------- request_hash: 대본 범위 A:N 전체 셀 ----------
def canon_cell(s):
    """셀 표기 차이(커넥터 vs 공개 CSV)를 흡수: 공백·줄바꿈 정리, 텍스트용 앞 작은따옴표 제거, 숫자는 2.0 -> 2."""
    s = norm("" if s is None else str(s))
    if s.startswith("'"):
        s = s[1:]
    if re.fullmatch(r"-?\d+(\.\d+)?", s):
        try:
            s = format(Decimal(s).normalize(), "f")
            if s in ("-0", ""):
                s = "0"
        except InvalidOperation:
            pass
    return s


def canon_rows(script_rows):
    out = []
    for r in script_rows:
        r = list(r)[:SCRIPT_COLS] + [""] * (SCRIPT_COLS - len(r))
        out.append([canon_cell(c) for c in r])
    return out


def check_script_range(episode_id, rng, rows):
    """요청한 대본 범위(rng=(시작,끝))가 실제 데이터와 맞는지: 행 개수 일치 + 모든 행의 A열이 요청 에피소드 ID. 오류 목록."""
    want = rng[1] - rng[0] + 1
    errs = []
    if len(rows) != want:
        errs.append("대본 범위 행 개수 불일치(요청 %d행, 실제 %d행)" % (want, len(rows)))
    bad = [i for i, r in enumerate(rows) if canon_cell(r[0] if r else "") != norm(episode_id)]
    if bad:
        errs.append("대본 범위의 A열이 요청 에피소드 ID(%s)와 다른 행이 %d개(범위 안 %s번째 등)" % (episode_id, len(bad), bad[0] + 1))
    return errs


def request_hash(episode_id, submitted_at, rng, d_text, script_rows):
    head = "\x1f".join([norm(episode_id), norm(submitted_at), norm(rng), norm(d_text)])
    body = "\x1e".join("\x1f".join(r) for r in canon_rows(script_rows))
    return hashlib.sha256((head + "\x1d" + body).encode("utf-8")).hexdigest()


def compute_verdict(results):
    if "불일치" in results:
        return "실패"
    if "보류" in results:
        return "수정필요"
    return "통과"


def clean_cell(s):
    """F열 한 줄 형식('번호|결과|URL|문장')을 깨지 않도록 구분자·줄바꿈 제거."""
    return re.sub(r"\s+", " ", (s or "").replace("|", "/")).strip()


# ---------- 결과 JSON 검증 (검수 실행 중복 판단과 Claude 반영 전 검증 공용) ----------
def validate_result(obj, req):
    """req = {episode_id, submitted_at, sheet_row, request_hash, items_count, urls:{번호: 원본 출처 URL}}. 오류 목록(빈 목록이면 유효)."""
    errs = []
    if not isinstance(obj, dict):
        return ["JSON 객체가 아님"]
    for k in ("schema_version", "episode_id", "submitted_at", "sheet_row", "request_hash", "verdict", "checks", "judged_at"):
        if k not in obj:
            errs.append("필수 필드 누락: " + k)
    if errs:
        return errs
    sv = obj["schema_version"]
    if isinstance(sv, bool) or not isinstance(sv, int) or sv not in SUPPORTED_SCHEMAS:
        errs.append("지원하지 않는 schema_version: %r (지원: %s)" % (sv, list(SUPPORTED_SCHEMAS)))
    if obj["episode_id"] != req["episode_id"]:
        errs.append("에피소드 ID 불일치")
    if obj["submitted_at"] != req["submitted_at"]:
        errs.append("제출 시각 불일치")
    if obj["sheet_row"] != req["sheet_row"]:
        errs.append("검수 탭 행 번호 불일치")
    if obj["request_hash"] != req["request_hash"]:
        errs.append("request_hash 불일치(대본·요청이 바뀌었거나 다른 요청의 결과)")
    checks = obj["checks"]
    if not isinstance(checks, list) or not checks:
        return errs + ["checks 비어 있음"]
    urls = req.get("urls")
    if not isinstance(urls, dict):
        errs.append("검증 맥락에 원본 출처 URL 목록이 없음")
        urls = {}
    nums = []
    for c in checks:
        if not isinstance(c, dict) or not isinstance(c.get("n"), int) or isinstance(c.get("n"), bool):
            errs.append("항목 번호가 정수가 아님")
            continue
        nums.append(c["n"])
        src, orig = str(c.get("src", "")), urls.get(c["n"])
        if c.get("result") not in RESULTS:
            errs.append("항목 %s: 결과값 오류" % c["n"])
        elif c["result"] in ("일치", "불일치"):
            # 일치·불일치 모두: src는 https여야 하고 해당 검수 항목의 원본 출처 URL과 정확히 같아야 함
            if not src.startswith("https://"):
                errs.append("항목 %s: %s인데 근거 URL(https)이 없음" % (c["n"], c["result"]))
            elif src != orig:
                errs.append("항목 %s: %s의 src가 원본 출처 URL과 다름" % (c["n"], c["result"]))
            if not str(c.get("evidence", "")).strip():
                errs.append("항목 %s: %s인데 근거 문장 없음" % (c["n"], c["result"]))
            if c.get("evidence_verified") is not True:
                errs.append("항목 %s: %s인데 근거 인용 검증 표시 없음" % (c["n"], c["result"]))
            need = "supports" if c["result"] == "일치" else "contradicts"
            if c.get("support_check") != need:
                errs.append("항목 %s: %s인데 연관성 평가가 %s가 아님" % (c["n"], c["result"], need))
        elif src not in ("", orig):
            errs.append("항목 %s: 보류인데 src가 비어 있지도 원본 출처 URL도 아님" % c["n"])
    if sorted(nums) != list(range(1, len(nums) + 1)) or len(set(nums)) != len(nums):
        errs.append("항목 번호 중복·누락: %s" % nums)
    if len(checks) != req["items_count"]:
        errs.append("항목 개수 불일치(요청 %s, 결과 %s)" % (req["items_count"], len(checks)))
    if not errs:
        if obj["verdict"] != compute_verdict([c["result"] for c in checks]):
            errs.append("판정값과 항목별 결과가 일치하지 않음")
    sub, jd = parse_iso(str(obj["submitted_at"])), parse_iso(str(obj["judged_at"]))
    now, tol = datetime.now(timezone.utc), timedelta(minutes=5)
    if sub is None:
        errs.append("제출 시각이 시간대 포함 ISO 8601이 아님")
    elif sub > now + tol:
        errs.append("제출 시각이 미래임")
    if jd is None:
        errs.append("판정 시각이 시간대 포함 ISO 8601이 아님")
    else:
        if jd > now + tol:
            errs.append("판정 시각이 미래임")
        if sub is not None and jd < sub - tol:
            errs.append("판정 시각이 제출 시각보다 앞섬")
    return errs


# ---------- 시트 읽기 (공개 CSV, 고정 주소) ----------
def http_get(url, timeout=40):
    rq = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (compatible; sports-inside-review)"})
    return urllib.request.urlopen(rq, timeout=timeout).read()


def read_csv(tab):
    url = "https://docs.google.com/spreadsheets/d/%s/gviz/tq?tqx=out:csv&sheet=%s" % (SHEET_ID, urllib.parse.quote(tab))
    raw = http_get(url, 60).decode("utf-8-sig")
    return list(csv.reader(io.StringIO(raw)))


# ---------- 출처 페이지: SSRF 방지 ----------
class UrlBlocked(Exception):
    pass


def resolve_host(host):
    infos = socket.getaddrinfo(host, 443, type=socket.SOCK_STREAM)
    return sorted({i[4][0].split("%")[0] for i in infos})


def blocked_ip(ip):
    a = ipaddress.ip_address(ip)
    if isinstance(a, ipaddress.IPv6Address) and a.ipv4_mapped:
        a = a.ipv4_mapped
    return (not a.is_global) or a.is_multicast or a.is_unspecified or a.is_loopback or a.is_link_local


def check_url(url):
    """허용되는 주소면 (host, 검증된 ip, 경로)를 돌려주고, 아니면 UrlBlocked."""
    p = urllib.parse.urlsplit((url or "").strip())
    if p.scheme != "https":
        raise UrlBlocked("https 주소만 허용")
    if p.username or p.password:
        raise UrlBlocked("주소에 계정 정보 포함")
    host = (p.hostname or "").lower().rstrip(".")
    if not host:
        raise UrlBlocked("호스트 없음")
    if host == "localhost" or host.endswith((".localhost", ".local", ".internal", ".localdomain", ".lan", ".home.arpa")):
        raise UrlBlocked("내부 호스트 이름")
    try:
        port = p.port or 443
    except ValueError:
        raise UrlBlocked("포트 형식 오류")
    if port != 443:
        raise UrlBlocked("443 포트만 허용")
    try:
        ipaddress.ip_address(host)
        ips = [host]
    except ValueError:
        try:
            ips = resolve_host(host)
        except Exception as e:
            raise UrlBlocked("주소 확인 실패: %s" % str(e)[:60])
    if not ips:
        raise UrlBlocked("주소 확인 실패")
    if any(blocked_ip(i) for i in ips):
        raise UrlBlocked("내부·사설·예약 주소로 연결됨")
    path = p.path or "/"
    if p.query:
        path += "?" + p.query
    return host, ips[0], path


class _Pinned(http.client.HTTPSConnection):
    """검증한 IP로만 접속(확인 후 이름이 다른 주소로 바뀌는 것을 방지). 인증서·SNI는 원래 호스트 이름 기준."""
    def __init__(self, host, ip, **kw):
        super().__init__(host, 443, **kw)
        self._ip = ip

    def connect(self):
        sock = socket.create_connection((self._ip, 443), self.timeout)
        self.sock = self._context.wrap_socket(sock, server_hostname=self.host)


def request_once(host, ip, path):
    """한 번 요청. 리다이렉션은 따라가지 않고 (상태, Location, Content-Type, 본문)만 돌려준다."""
    conn = _Pinned(host, ip, timeout=30, context=ssl.create_default_context())
    try:
        conn.request("GET", path, headers={"User-Agent": "Mozilla/5.0 (compatible; sports-inside-review)",
                                           "Accept": "text/html,application/xhtml+xml,text/plain;q=0.9,*/*;q=0.5",
                                           "Accept-Encoding": "identity"})
        r = conn.getresponse()
        body = r.read(MAX_BYTES + 1) if r.status == 200 else b""   # 한도보다 1바이트 더 읽어 초과 여부를 감지
        return r.status, r.getheader("Location"), r.getheader("Content-Type", ""), body
    finally:
        conn.close()


_page_cache = {}
PARTIAL = set()   # 본문이 길어 앞부분만 모델에 준 URL(이런 페이지는 불일치 판정 금지)


def html_to_text(raw):
    raw = re.sub(r"(?is)<(script|style|noscript|nav|footer|header|svg)[^>]*>.*?</\1>", " ", raw)
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"(?s)<[^>]+>", " ", raw))).strip()


def fetch_text(url):
    """(본문 텍스트, 오류사유). 리다이렉션마다 도착지를 다시 검증한다. 실패하면 ('', 사유)."""
    if url in _page_cache:
        return _page_cache[url]
    out = ("", "접근 실패")
    cur = url
    try:
        for hop in range(MAX_REDIRECTS + 1):
            host, ip, path = check_url(cur)          # 매 이동마다 https·내부 주소 재검증
            res = None
            for attempt in range(2):
                try:
                    res = request_once(host, ip, path)
                    break
                except Exception as e:
                    out = ("", "접근 실패: %s" % str(e)[:80])
                    time.sleep(2)
            if res is None:
                break
            status, loc, ctype, body = res
            if status in (301, 302, 303, 307, 308) and loc:
                cur = urllib.parse.urljoin(cur, loc)
                continue
            if status != 200:
                out = ("", "접근 실패: HTTP %d" % status)
                break
            if ctype and not re.search(r"(text/|html|xml|json)", ctype, re.I):
                out = ("", "텍스트가 아닌 형식: %s" % ctype[:40])
                break
            if len(body) > MAX_BYTES:   # 한도 초과: 일부만 읽은 내용으로 판정하지 않고 통째로 보류
                out = ("", "페이지가 %dMB를 넘어 전체를 읽을 수 없어 보류" % (MAX_BYTES // 1_000_000))
                break
            m = re.search(r"charset=([\w-]+)", ctype or "", re.I)
            try:
                raw = body.decode(m.group(1) if m else "utf-8", "ignore")
            except LookupError:
                raw = body.decode("utf-8", "ignore")
            text = html_to_text(raw)
            if len(text) < MIN_PAGE_CHARS:
                out = ("", "본문 부족(JS 렌더링·유료 페이지 가능)")
            else:
                if len(text) > MAX_PAGE_CHARS:
                    PARTIAL.add(url)
                out = (text[:MAX_PAGE_CHARS], "")
            break
        else:
            out = ("", "접근 실패: 리다이렉션이 너무 많음")
    except UrlBlocked as e:
        out = ("", "차단: %s" % e)
    _page_cache[url] = out
    return out


# ---------- 모델 ----------
JUDGE_SYSTEM = """당신은 한국어 스포츠 쇼츠 대본의 독립 사실 검수자입니다. 사실 한 줄(CLAIM)이 제공된 출처 본문(PAGE)과 맞는지만 판정합니다.
규칙:
- PAGE에 적힌 내용만 근거로 삼는다. 당신의 기존 지식과 맞다는 이유로 '일치'를 내지 않는다.
- 수치·연도·이름·팀·대상·범위·인과관계를 모두 대조한다. 하나라도 PAGE로 확인되지 않으면 '보류'.
- CLAIM 끝의 괄호 설명은 작성자 메모이니 핵심 주장만 판정한다.
- '일치': PAGE가 CLAIM 전체를 뒷받침한다. '불일치': PAGE가 CLAIM과 명백히 다르게 말한다(수치·연도·주체가 다름). PAGE에 언급이 없거나 애매하면 불일치가 아니라 '보류'.
- quote에는 판단의 근거가 된 PAGE 속 문장을 **PAGE에 있는 그대로**(번역·요약·수정 없이) 복사한다. 300자 이내. 보류면 빈 문자열.
JSON 객체만 출력: {"result":"일치|불일치|보류","quote":"","reason":"한 문장"}"""

SUPPORT_SYSTEM = """당신은 근거 연관성 검사자입니다. 주장(CLAIM)과 출처 발췌(EXCERPT)만 보고 둘의 관계를 판정합니다. 당신의 기존 지식은 쓰지 않습니다.
- supports: EXCERPT가 CLAIM의 구체 내용(수치·연도·주체·범위·인과)을 모두 직접 뒷받침한다.
- contradicts: EXCERPT가 CLAIM의 수치·연도·주체와 명백히 반대되는 내용을 말한다.
- insufficient: 주제는 관련되지만 일부만 다루거나 추론·가정이 필요하다.
- unrelated: CLAIM과 무관한 내용이다.
CLAIM 끝의 괄호 설명은 작성자 메모이니 핵심 주장만 본다. 확신이 없으면 insufficient.
JSON 객체만 출력: {"relation":"supports|contradicts|insufficient|unrelated","reason":"한 문장"}"""


def _chat(system, user):
    key = os.environ["OPENAI_API_KEY"]
    body = {"model": MODEL, "temperature": 0, "response_format": {"type": "json_object"},
            "messages": [{"role": "system", "content": system}, {"role": "user", "content": user}]}
    last = None
    for attempt in range(3):
        try:
            rq = urllib.request.Request("https://api.openai.com/v1/chat/completions", json.dumps(body).encode(),
                                        {"Authorization": "Bearer " + key, "Content-Type": "application/json"})
            r = json.loads(urllib.request.urlopen(rq, timeout=240).read())
            return json.loads(r["choices"][0]["message"]["content"])
        except Exception as e:
            last = e
            time.sleep(5 * (attempt + 1))
    raise RuntimeError("모델 호출 실패: %s" % str(last)[:100])


def llm_judge(claim, page):
    return _chat(JUDGE_SYSTEM, "CLAIM: %s\n\nPAGE:\n%s" % (claim, page))


def llm_support(claim, excerpt):
    return _chat(SUPPORT_SYSTEM, "CLAIM: %s\n\nEXCERPT:\n%s" % (claim, excerpt))


def context_window(page, quote, pad=600):
    f = fold(page)
    q = fold(quote)
    i = f.find(q)
    return f[max(0, i - pad): i + len(q) + pad]


def _hold(n, reason):
    return {"n": n, "result": "보류", "src": "", "evidence": "", "evidence_verified": False, "support_check": "", "reason": reason}


def check_item(n, claim, url):
    """한 항목 판정. 코드가 확인할 수 없거나 근거가 불충분하면 항상 보류."""
    page, why = fetch_text(url)
    if not page:
        return _hold(n, why)
    j = llm_judge(claim, page)
    res, quote = j.get("result"), (j.get("quote") or "").strip()
    reason = str(j.get("reason", ""))[:200]
    if res not in RESULTS:
        return _hold(n, "모델 응답 형식 오류")
    if res == "보류":
        return _hold(n, reason or "출처에서 확인 불가")
    if res == "불일치" and url in PARTIAL:   # 앞부분만 본 상태에서 '다르다'고 단정하지 않음(뒤에 정정 내용이 있을 수 있음)
        return _hold(n, "본문이 길어 앞부분만 검토해 불일치로 단정할 수 없어 보류")
    # 1) 인용문 존재 여부: 코드가 원문에서 직접 확인
    if len(fold(quote)) < 10 or fold(quote) not in fold(page):
        return _hold(n, "근거 인용문이 출처 본문에서 확인되지 않아 보류(모델 판정: %s)" % res)
    # 2) 주장 뒷받침 여부: 인용문 주변 발췌만 보고 따로 평가(앞선 판정 결과는 알려주지 않음)
    rel = str(llm_support(claim, context_window(page, quote)).get("relation", ""))
    need = "supports" if res == "일치" else "contradicts"
    if rel != need:
        return _hold(n, "인용문은 있으나 주장을 직접 %s하지 못해 보류(모델 판정: %s, 연관성 평가: %s)" % (
            "뒷받침" if res == "일치" else "반박", res, rel))
    return {"n": n, "result": res, "src": url, "evidence": quote[:300], "evidence_verified": True,
            "support_check": rel, "reason": reason}


# ---------- 실행 ----------
def find_targets(rows, now):
    """검수 탭에서 대상 행 선택: A·D 있음, E·H 비어 있음, 제출 후 35시간 이내."""
    targets, skipped = [], []
    if not rows or not rows[0] or norm(rows[0][0]) != "에피소드ID":
        raise RuntimeError("검수 탭 머리글을 확인하지 못함(A1이 '에피소드ID'가 아님)")
    for i, r in enumerate(rows[1:], start=2):
        r = list(r) + [""] * (8 - len(r))
        a, b, c, d, e, h = (norm(r[0]), norm(r[1]), norm(r[2]), r[3], norm(r[4]), norm(r[7]))
        if not a or not norm(d):
            continue
        if e or h:
            skipped.append((a, i, "이미 판정/반영됨"))
            continue
        sub = parse_iso(b)
        if sub is None:
            skipped.append((a, i, "제출 시각 형식 오류"))
            continue
        if sub > now + timedelta(minutes=5):
            skipped.append((a, i, "제출 시각이 미래"))
            continue
        if now - sub > timedelta(hours=MAX_AGE_H):
            skipped.append((a, i, "제출 후 %d시간 초과" % MAX_AGE_H))
            continue
        targets.append({"episode_id": a, "submitted_at": b, "range": c, "D": d, "sheet_row": i})
    return targets, skipped


def out_name(t, h):
    return "%s_r%d_%s.json" % (t["episode_id"], t["sheet_row"], h[:8])


def run(out_dir):
    now = datetime.now(KST)
    summary = {"at": now_kst(), "reviewed": [], "skipped": [], "errors": []}
    os.makedirs(out_dir, exist_ok=True)
    rows = read_csv("검수")
    targets, skipped = find_targets(rows, now)
    summary["skipped"] += ["%s(행%d): %s" % s for s in skipped]
    script_rows = None
    for t in targets:
        try:
            rng = parse_range(t["range"])
            if not rng:
                raise ValueError("대본 범위 형식 오류: %s" % t["range"])
            items = parse_items(t["D"])
            if script_rows is None:
                script_rows = read_csv("Untitled")
            if rng[1] > len(script_rows):   # 존재하지 않는 행을 빈 칸으로 대신 채우지 않고 검수를 중단
                raise ValueError("요청한 대본 범위(%s)가 시트 실제 데이터(%d행)를 벗어남" % (t["range"], len(script_rows)))
            sc = script_rows[rng[0] - 1: rng[1]]
            rerrs = check_script_range(t["episode_id"], rng, sc)
            if rerrs:
                raise ValueError("대본 범위 검증 실패: " + "; ".join(rerrs))
            h = request_hash(t["episode_id"], t["submitted_at"], t["range"], t["D"], sc)
            req = {"episode_id": t["episode_id"], "submitted_at": t["submitted_at"], "sheet_row": t["sheet_row"],
                   "request_hash": h, "items_count": len(items), "urls": {n: u for n, _, u in items}}
            path = os.path.join(out_dir, out_name(t, h))
            if os.path.exists(path):
                try:
                    if not validate_result(json.load(open(path, encoding="utf-8")), req):
                        summary["skipped"].append("%s(행%d): 이미 유효한 결과 있음" % (t["episode_id"], t["sheet_row"]))
                        continue
                except Exception:
                    pass  # 손상된 파일은 다시 검수해 덮어씀
            checks = [check_item(n, claim, url) for n, claim, url in items]
            obj = {"schema_version": SCHEMA_VERSION, "episode_id": t["episode_id"], "submitted_at": t["submitted_at"],
                   "sheet_row": t["sheet_row"], "request_hash": h,
                   "verdict": compute_verdict([c["result"] for c in checks]), "checks": checks,
                   "judged_at": now_kst(), "model": MODEL}
            errs = validate_result(obj, req)
            if errs:
                raise RuntimeError("생성한 결과가 자체 검증에 실패: %s" % errs)
            tmp = path + ".tmp"
            json.dump(obj, open(tmp, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
            os.replace(tmp, path)
            summary["reviewed"].append("%s(행%d): %s" % (t["episode_id"], t["sheet_row"], obj["verdict"]))
        except Exception as e:
            summary["errors"].append("%s(행%d): %s" % (t["episode_id"], t["sheet_row"], str(e)[:200]))
    json.dump(summary, open(os.path.join(out_dir, "_last_run.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 1 if summary["errors"] else 0


# ---------- Claude 반영 전 검증 (verify / select) ----------
def verify(result_path, ctx_path):
    """ctx = {episode_id, submitted_at(B), range(C), D, sheet_row, script:[A:N 14칸 행...], hub_items:[{t,src}...]}.
    결과: {ok, errors, E, F, G}. ok일 때만 E(판정)·F(항목별 결과 줄)·G(판정 시각)를 시트에 쓴다."""
    ctx = json.load(open(ctx_path, encoding="utf-8"))
    try:
        obj = json.load(open(result_path, encoding="utf-8"))
    except Exception as e:
        return {"ok": False, "errors": ["JSON 읽기 실패: %s" % str(e)[:80]]}
    try:
        items = parse_items(ctx["D"])
    except ValueError as e:
        return {"ok": False, "errors": [str(e)]}
    errs = []
    rng = parse_range(ctx.get("range", ""))
    if not rng:
        errs.append("대본 범위 형식 오류: %s" % ctx.get("range"))
    elif not isinstance(ctx.get("script"), list):
        errs.append("맥락에 대본 행(script)이 없음")
    else:
        errs += check_script_range(ctx["episode_id"], rng, ctx["script"])
    # 허브 items[]와 D열을 번호별로 내용·출처 URL까지 비교
    hub = ctx.get("hub_items")
    if not isinstance(hub, list):
        errs.append("맥락에 hub_items가 없음")
    else:
        if len(hub) != len(items):
            errs.append("허브 items 개수(%d)와 검수 요청 항목 개수(%d) 불일치" % (len(hub), len(items)))
        for (n, claim, url), h in zip(items, hub):
            if fold(strip_tail(str(h.get("t", "")))) != fold(claim):
                errs.append("항목 %d: 허브 items의 주장 내용이 D열과 다름" % n)
            if str(h.get("src", "")).strip() != url:
                errs.append("항목 %d: 허브 items의 출처 URL이 D열과 다름" % n)
    if errs:   # 범위·맥락이 틀리면 해시 계산 없이 중단
        return {"ok": False, "errors": errs}
    rh = request_hash(ctx["episode_id"], ctx["submitted_at"], ctx["range"], ctx["D"], ctx["script"])
    req = {"episode_id": ctx["episode_id"], "submitted_at": ctx["submitted_at"], "sheet_row": ctx["sheet_row"],
           "request_hash": rh, "items_count": len(items), "urls": {n: u for n, _, u in items}}
    errs += validate_result(obj, req)
    if errs:
        return {"ok": False, "errors": errs}
    checks = sorted(obj["checks"], key=lambda c: c["n"])
    f = "\n".join("%d|%s|%s|%s" % (c["n"], c["result"], clean_cell(c.get("src", "")), clean_cell(c.get("evidence", "")))
                  for c in checks)
    return {"ok": True, "errors": [], "E": compute_verdict([c["result"] for c in checks]), "F": f, "G": obj["judged_at"]}


def select(result_paths, ctx_path):
    """같은 에피소드·행의 후보 JSON이 여러 개일 때: 모두 verify해 현재 요청과 맞는 것만 유효 후보로 인정.
    status: none(후보 없음) | ok(유효 1개) | multiple(유효 여러 개: 오류, 임의 선택 안 함) | invalid(후보는 있으나 유효한 것이 없음)."""
    if not result_paths:
        return {"status": "none", "ok": False, "errors": []}
    valid, bad = [], []
    for p in result_paths:
        r = verify(p, ctx_path)
        (valid if r["ok"] else bad).append((p, r))
    if len(valid) > 1:
        return {"status": "multiple", "ok": False, "files": [os.path.basename(p) for p, _ in valid],
                "errors": ["현재 요청과 맞는 유효 JSON이 %d개라 임의로 선택하지 않음: %s" % (
                    len(valid), ", ".join(os.path.basename(p) for p, _ in valid))]}
    if len(valid) == 1:
        p, r = valid[0]
        return {"status": "ok", "ok": True, "file": os.path.basename(p), "errors": [], "E": r["E"], "F": r["F"], "G": r["G"]}
    return {"status": "invalid", "ok": False,
            "errors": ["%s: %s" % (os.path.basename(p), "; ".join(r["errors"])) for p, r in bad]}


def main(argv=None):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--out", default="review")
    v = sub.add_parser("verify")
    v.add_argument("--json", required=True)
    v.add_argument("--ctx", required=True)
    s = sub.add_parser("select")
    s.add_argument("--ctx", required=True)
    s.add_argument("--json", nargs="*", default=[])
    a = ap.parse_args(argv)
    if a.cmd == "run":
        return run(a.out)
    if a.cmd == "verify":
        res = verify(a.json, a.ctx)
        print(json.dumps(res, ensure_ascii=False))
        return 0 if res["ok"] else 2
    res = select(a.json, a.ctx)
    print(json.dumps(res, ensure_ascii=False))
    return 0 if res["status"] == "ok" else (3 if res["status"] == "none" else 2)


if __name__ == "__main__":
    sys.exit(main())
