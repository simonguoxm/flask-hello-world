# -*- coding: utf-8 -*-
"""
麻将比赛管理系统 - 后端服务
单场比赛使用,数据全部存于内存,不持久化,不做登录权限控制。

赛制说明:
1. Preliminary(预赛):全员参赛,固定轮次,每轮随机分桌(尽量避免同桌重复)
2. 预赛结束按累计 Table Point(Game Point 为 Tie Break)取前 8 名晋级
3. Semi-final(半决赛):前 8 名固定分成 A/B 两桌(种子分桌 1,4,5,8 / 2,3,6,7),
   打若干轮;其他未晋级选手继续打,但用避重算法随机分桌,不计入正式排名
4. 半决赛结束,A/B 两桌各自前 2 名进"冠军组",后 2 名进"附加组"
5. Final(决赛):冠军组 4 人固定一桌决出 1-4 名,附加组 4 人固定一桌决出 5-8 名;
   其他选手继续打但不计入正式排名
6. 计分:每桌按 Game Point 排名,赋予 Table Point(4/2/1/0),Game Point 累计作为 Tie Break
"""

import random
import itertools
from flask import Flask, request, jsonify, render_template

app = Flask(__name__)
app.json.sort_keys = False

TABLE_POINTS = [4, 2, 1, 0]

# ---------------------------------------------------------------------------
# 全局状态(单场比赛,内存存储)
# ---------------------------------------------------------------------------

def fresh_state():
    return {
        "stage": "setup",  # setup -> preliminary -> semifinal -> final -> finished
        "config": {
            "preliminaryRounds": 6,
            "semifinalRounds": 1,
            "finalRounds": 1,
        },
        "tournamentName": "",
        "players": {},       # id -> {id, name}
        "currentRound": 0,   # 当前阶段内的轮次号(从 1 开始计数,0 表示还没开始)
        "rounds": [],        # 历史 + 当前轮次记录
        "pairHistory": {},   # "id1-id2" -> 同桌次数(全程累计,用于避重)
        "qualifiers": [],    # 预赛结束后的前 8 名 id,按名次排序
        "semifinalTables": {"A": [], "B": []},      # 半决赛固定分桌
        "finalTables": {"champion": [], "consolation": []},  # 决赛固定分桌
        "finalRanking": [],  # 比赛结束后的最终 1-8 名 id 列表
    }

STATE = fresh_state()


# ---------------------------------------------------------------------------
# 工具函数
# ---------------------------------------------------------------------------

def pair_key(a, b):
    return "-".join(str(x) for x in sorted([a, b]))


def record_pair_history(table_ids):
    for a, b in itertools.combinations(table_ids, 2):
        key = pair_key(a, b)
        STATE["pairHistory"][key] = STATE["pairHistory"].get(key, 0) + 1


def pair_cost(table_ids):
    cost = 0
    for a, b in itertools.combinations(table_ids, 2):
        cost += STATE["pairHistory"].get(pair_key(a, b), 0)
    return cost


def generate_tables_avoiding_repeat(player_ids, attempts=80):
    """
    改进的分桌算法:
    1. 二次惩罚(count²):重复同桌的代价指数级增加,算法更主动地把未见过的人分在一起
    2. 2-opt 局部搜索:每次初始分组后尝试所有跨桌两两交换,直到局部最优
    3. 混合初始化:75% 按"隔离度"排序(见过最少不同对手的人优先分在一起),25% 纯随机
    """
    ids = list(player_ids)
    if len(ids) % 4 != 0:
        raise ValueError("人数必须是 4 的倍数")

    def pair_score(a, b):
        c = STATE["pairHistory"].get(pair_key(a, b), 0)
        return c * c  # 二次惩罚

    def table_score(table):
        s = 0
        for i in range(len(table)):
            for j in range(i + 1, len(table)):
                s += pair_score(table[i], table[j])
        return s

    def local_search(tables):
        """跨桌两两交换,保留能降低总分的交换,反复迭代直到无法改进。"""
        tables = [list(t) for t in tables]
        improved = True
        while improved:
            improved = False
            for ti in range(len(tables)):
                for tj in range(ti + 1, len(tables)):
                    old = table_score(tables[ti]) + table_score(tables[tj])
                    for pi in range(4):
                        for pj in range(4):
                            tables[ti][pi], tables[tj][pj] = tables[tj][pj], tables[ti][pi]
                            new = table_score(tables[ti]) + table_score(tables[tj])
                            if new < old:
                                old = new
                                improved = True
                            else:
                                tables[ti][pi], tables[tj][pj] = tables[tj][pj], tables[ti][pi]
        return tables

    # 预计算每位选手"见过的不同对手数量"(隔离度越低 = 越需要新的对阵)
    def isolation(pid):
        return sum(
            1 for o in ids if o != pid
            and STATE["pairHistory"].get(pair_key(pid, o), 0) > 0
        )

    best_tables = None
    best_score = None

    for attempt in range(attempts):
        if attempt % 4 != 3:
            # 按隔离度升序排(见过最少对手的人排前面),加随机扰动避免每次完全相同
            shuffled = sorted(ids, key=lambda p: (isolation(p), random.random()))
        else:
            shuffled = ids[:]
            random.shuffle(shuffled)

        tables = [shuffled[i:i + 4] for i in range(0, len(shuffled), 4)]
        tables = local_search(tables)
        s = sum(table_score(t) for t in tables)

        if best_score is None or s < best_score:
            best_score = s
            best_tables = [list(t) for t in tables]
            if best_score == 0:
                break

    return best_tables


def compute_table_points(game_points):
    """game_points: list of (playerId, gamePoint) -> dict playerId -> tablePoint(并列取均分)"""
    ordered = sorted(game_points, key=lambda x: -x[1])
    n = len(ordered)
    result = {}
    i = 0
    while i < n:
        j = i
        while j + 1 < n and ordered[j + 1][1] == ordered[i][1]:
            j += 1
        share = round(sum(TABLE_POINTS[i:j + 1]) / (j - i + 1), 1)
        for k in range(i, j + 1):
            result[ordered[k][0]] = share
        i = j + 1
    return result


def player_name(pid):
    p = STATE["players"].get(pid)
    return p["name"] if p else "?"


def stage_rounds(stage):
    return [r for r in STATE["rounds"] if r["stage"] == stage]


def player_totals_for_stage(stage, player_ids=None):
    """返回 {playerId: {"tp":..., "gp":...}},仅统计已提交的轮次"""
    totals = {}
    ids = player_ids if player_ids is not None else STATE["players"].keys()
    for pid in ids:
        totals[pid] = {"tp": 0.0, "gp": 0}
    for rnd in stage_rounds(stage):
        for table in rnd["tables"]:
            if not table.get("submitted"):
                continue
            for res in table["results"]:
                pid = res["playerId"]
                if pid in totals:
                    totals[pid]["tp"] += res["tablePoint"]
                    totals[pid]["gp"] += res["gamePoint"]
    return totals


def ranked_player_ids(player_ids=None):
    """排名用的选手过滤:
    - 无指定时: 只含 active 选手(drop 和 bye 均排除)
    - 有指定时(如固定桌): 只排除 bye
    """
    if player_ids is None:
        return [pid for pid, p in STATE["players"].items()
                if p.get("status", "active") == "active"]
    return [pid for pid in player_ids
            if STATE["players"].get(pid, {}).get("status", "active") != "bye"]


def player_totals_multi(stages, player_ids=None):
    """统计跨多个阶段的累计 Table Point / Game Point(用于陪打选手全程累计成绩)。"""
    ids = player_ids if player_ids is not None else list(STATE["players"].keys())
    totals = {pid: {"tp": 0.0, "gp": 0} for pid in ids}
    for rnd in STATE["rounds"]:
        if rnd["stage"] not in stages:
            continue
        for table in rnd["tables"]:
            if not table.get("submitted"):
                continue
            for res in table["results"]:
                pid = res["playerId"]
                if pid in totals:
                    totals[pid]["tp"] += res["tablePoint"]
                    totals[pid]["gp"] += res["gamePoint"]
    return totals


def standings_for_stage(stage, player_ids=None):
    ids = ranked_player_ids(player_ids)
    totals = player_totals_for_stage(stage, ids)
    rows = []
    for pid, t in totals.items():
        rows.append({
            "playerId": pid,
            "name": player_name(pid),
            "tablePoint": round(t["tp"], 1),
            "gamePoint": round(t["gp"], 1),
        })
    rows.sort(key=lambda r: (-r["tablePoint"], -r["gamePoint"]))
    return rows


def standings_multi(stages, player_ids=None):
    ids = ranked_player_ids(player_ids)
    totals = player_totals_multi(stages, ids)
    rows = []
    for pid, t in totals.items():
        rows.append({
            "playerId": pid,
            "name": player_name(pid),
            "tablePoint": round(t["tp"], 1),
            "gamePoint": round(t["gp"], 1),
        })
    rows.sort(key=lambda r: (-r["tablePoint"], -r["gamePoint"]))
    return rows


def current_unsubmitted_round():
    if not STATE["rounds"]:
        return None
    last = STATE["rounds"][-1]
    if last["stage"] != STATE["stage"] or last["roundNumber"] != STATE["currentRound"]:
        return None
    if all(t["submitted"] for t in last["tables"]):
        return None
    return last


def all_active_player_ids():
    return list(STATE["players"].keys())


def fixed_tables_for_stage(stage):
    """返回该阶段需要固定座位的桌次列表 [[ids...], ...] 和已占用的人员集合"""
    if stage == "semifinal":
        tables = []
        if STATE["semifinalTables"]["A"]:
            tables.append(STATE["semifinalTables"]["A"])
        if STATE["semifinalTables"]["B"]:
            tables.append(STATE["semifinalTables"]["B"])
        return tables
    if stage == "final":
        tables = []
        if STATE["finalTables"]["champion"]:
            tables.append(STATE["finalTables"]["champion"])
        if STATE["finalTables"]["consolation"]:
            tables.append(STATE["finalTables"]["consolation"])
        return tables
    return []


def build_final_summary():
    """返回完整成绩汇总:每位选手在每一轮的 TP/GP,以及各阶段小计和总计,按最终排名排序。"""
    stages = ["preliminary", "semifinal", "final"]

    # 按 finalRanking 顺序输出(已排除 bye),再补充其他非 bye 选手
    ordered_ids = list(STATE["finalRanking"])
    remaining = [pid for pid in STATE["players"]
                 if pid not in ordered_ids
                 and STATE["players"][pid].get("status", "active") != "bye"]
    ordered_ids += remaining

    # 收集各阶段的轮次列表(已提交且有顺序)
    stage_rounds = {s: [] for s in stages}
    for rnd in STATE["rounds"]:
        if rnd["stage"] in stage_rounds:
            stage_rounds[rnd["stage"]].append(rnd)

    summary = []
    for rank, pid in enumerate(ordered_ids, 1):
        name = player_name(pid)
        rounds_data = []
        stage_totals = {}

        for s in stages:
            s_tp = 0.0
            s_gp = 0.0
            for rnd in stage_rounds[s]:
                rnd_tp = None
                rnd_gp = None
                for table in rnd["tables"]:
                    if not table.get("submitted"):
                        continue
                    for res in table["results"]:
                        if res["playerId"] == pid:
                            rnd_tp = res["tablePoint"]
                            rnd_gp = res["gamePoint"]
                if rnd_tp is not None:
                    s_tp += rnd_tp
                    s_gp += rnd_gp
                rounds_data.append({
                    "stage": s,
                    "round": rnd["roundNumber"],
                    "tablePoint": round(rnd_tp, 1) if rnd_tp is not None else "-",
                    "gamePoint": round(rnd_gp, 1) if rnd_gp is not None else "-",
                })
            stage_totals[s] = {
                "tablePoint": round(s_tp, 1),
                "gamePoint": round(s_gp, 1),
            }

        total_tp = round(sum(v["tablePoint"] for v in stage_totals.values()), 1)
        total_gp = round(sum(v["gamePoint"] for v in stage_totals.values()), 1)

        summary.append({
            "rank": rank,
            "playerId": pid,
            "name": name,
            "rounds": rounds_data,
            "stageTotals": stage_totals,
            "totalTablePoint": total_tp,
            "totalGamePoint": total_gp,
        })
    return summary

@app.route("/")
def index():
    return render_template("admin.html")


@app.route("/admin")
def admin_page():
    return render_template("admin.html")


@app.route("/display")
def display_page():
    return render_template("display.html")


# ---------------------------------------------------------------------------
# API - 状态查询
# ---------------------------------------------------------------------------

@app.route("/api/state")
def api_state():
    stage = STATE["stage"]

    payload = {
        "stage": stage,
        "config": STATE["config"],
        "tournamentName": STATE.get("tournamentName", ""),
        "currentRound": STATE["currentRound"],
        "players": [{"id": pid, "name": p["name"], "status": p.get("status","active")}
                    for pid, p in STATE["players"].items()],
        "qualifiers": STATE["qualifiers"],
        "finalRanking": STATE["finalRanking"],
    }

    # 当前轮次的分桌情况(用于展示座位表 + 录入成绩)
    rnd = STATE["rounds"][-1] if STATE["rounds"] else None
    if rnd and rnd["stage"] == stage and rnd["roundNumber"] == STATE["currentRound"]:
        fixed_ids_set = set()
        for ids in fixed_tables_for_stage(stage):
            fixed_ids_set.update(ids)
        payload["currentRoundData"] = {
            "stage": rnd["stage"],
            "roundNumber": rnd["roundNumber"],
            "tables": [
                {
                    "tableId": t["tableId"],
                    "label": t["label"],
                    "playerIds": t["playerIds"],
                    "playerNames": [player_name(pid) for pid in t["playerIds"]],
                    "playerStatuses": [STATE["players"][pid].get("status","active") for pid in t["playerIds"]],
                    "submitted": t["submitted"],
                    "results": t["results"],
                    "isFixed": any(pid in fixed_ids_set for pid in t["playerIds"]),
                }
                for t in rnd["tables"]
            ],
        }
    else:
        payload["currentRoundData"] = None

    # 排名榜:根据阶段返回相应的排名信息
    if stage == "preliminary":
        payload["standings"] = {"preliminary": standings_for_stage("preliminary")}
    elif stage == "semifinal":
        top8 = STATE["qualifiers"]
        others = [pid for pid in STATE["players"] if pid not in top8]
        payload["standings"] = {
            "semifinalA": standings_for_stage("semifinal", STATE["semifinalTables"]["A"]),
            "semifinalB": standings_for_stage("semifinal", STATE["semifinalTables"]["B"]),
            "others": standings_multi(["preliminary", "semifinal"], others),
        }
    elif stage == "final":
        champ = STATE["finalTables"]["champion"]
        consol = STATE["finalTables"]["consolation"]
        others = [pid for pid in STATE["players"] if pid not in champ and pid not in consol]
        payload["standings"] = {
            "champion": standings_for_stage("final", champ),
            "consolation": standings_for_stage("final", consol),
            "others": standings_multi(["preliminary", "semifinal", "final"], others),
        }
    elif stage == "finished":
        payload["standings"] = {}
        payload["finalRankingNames"] = [player_name(pid) for pid in STATE["finalRanking"]]
        payload["finalSummary"] = build_final_summary()

    return jsonify(payload)


# ---------------------------------------------------------------------------
# API - 初始化 / 重置
# ---------------------------------------------------------------------------

@app.route("/api/setup", methods=["POST"])
def api_setup():
    data = request.get_json(force=True)
    names = [n.strip() for n in data.get("names", []) if n.strip()]
    if len(names) < 4:
        return jsonify({"error": "至少需要 4 名选手"}), 400

    global STATE
    STATE = fresh_state()
    for i, name in enumerate(names):
        pid = i + 1
        STATE["players"][pid] = {"id": pid, "name": name, "status": "active"}

    STATE["tournamentName"] = data.get("tournamentName", "").strip()
    cfg = data.get("config", {})
    STATE["config"]["preliminaryRounds"] = int(cfg.get("preliminaryRounds", 6))
    STATE["config"]["semifinalRounds"] = int(cfg.get("semifinalRounds", 2))
    STATE["config"]["finalRounds"] = int(cfg.get("finalRounds", 2))

    STATE["stage"] = "preliminary"
    STATE["currentRound"] = 0
    return jsonify({"ok": True})


@app.route("/api/reset", methods=["POST"])
def api_reset():
    global STATE
    STATE = fresh_state()
    return jsonify({"ok": True})


@app.route("/api/player/status", methods=["POST"])
def api_player_status():
    data = request.get_json(force=True)
    pid = int(data.get("playerId"))
    status = data.get("status")
    if status not in ("active", "drop", "bye"):
        return jsonify({"error": "状态必须是 active / drop / bye"}), 400
    player = STATE["players"].get(pid)
    if not player:
        return jsonify({"error": "找不到该选手"}), 400
    player["status"] = status
    return jsonify({"ok": True, "playerId": pid, "status": status})


# ---------------------------------------------------------------------------
# API - 轮次生成 / 成绩提交
# ---------------------------------------------------------------------------

@app.route("/api/round/generate", methods=["POST"])
def api_round_generate():
    stage = STATE["stage"]
    if stage not in ("preliminary", "semifinal", "final"):
        return jsonify({"error": "当前阶段不能生成轮次"}), 400

    if current_unsubmitted_round() is not None:
        return jsonify({"error": "当前轮次尚未提交完成,不能生成新轮次"}), 400

    max_rounds = STATE["config"][stage + "Rounds"]
    if STATE["currentRound"] >= max_rounds:
        return jsonify({"error": "本阶段轮次已打满,请进入下一阶段"}), 400

    STATE["currentRound"] += 1

    fixed = fixed_tables_for_stage(stage)
    fixed_ids = set()
    tables = []
    table_counter = 1

    labels = {"semifinal": ["冠军争夺组 (A桌)", "冠军争夺组 (B桌)"],
              "final": ["决赛冠军桌 (1-4名)", "决赛附加桌 (5-8名)"]}

    for idx, ids in enumerate(fixed):
        fixed_ids.update(ids)
        label = labels.get(stage, ["固定桌"])[idx] if idx < len(labels.get(stage, [])) else f"固定桌{idx+1}"
        tables.append({
            "tableId": table_counter,
            "label": label,
            "playerIds": ids,
            "submitted": False,
            "results": [],
        })
        table_counter += 1

    # 非固定桌的选手:按 status 分类
    all_non_fixed = [pid for pid in STATE["players"].keys() if pid not in fixed_ids]
    active_pool = [pid for pid in all_non_fixed
                   if STATE["players"][pid].get("status", "active") == "active"]
    bye_pool    = [pid for pid in all_non_fixed
                   if STATE["players"][pid].get("status", "active") == "bye"]
    # drop 选手不参与

    n_active = len(active_pool)
    need_byes = (4 - n_active % 4) % 4

    if need_byes > 0 and len(bye_pool) < need_byes:
        return jsonify({
            "error": f"Active 选手 {n_active} 人,需要 {need_byes} 个 bye 凑成 4 的倍数,"
                     f"但只有 {len(bye_pool)} 个 bye 选手可用。请调整选手状态。"
        }), 400

    # 轮转选择 bye:优先选本阶段上场次数最少的 bye
    bye_round_counts = {}
    for pid in bye_pool:
        cnt = 0
        for rnd in STATE["rounds"]:
            if rnd["stage"] != stage:
                continue
            for t in rnd["tables"]:
                if pid in t["playerIds"]:
                    cnt += 1
        bye_round_counts[pid] = cnt
    bye_pool_sorted = sorted(bye_pool, key=lambda pid: bye_round_counts[pid])
    selected_byes = bye_pool_sorted[:need_byes]

    remaining = active_pool + selected_byes
    if remaining:
        if len(remaining) % 4 != 0:
            return jsonify({"error": "内部错误:分组后人数仍不是 4 的倍数"}), 400
        random_tables = generate_tables_avoiding_repeat(remaining)
        for ids in random_tables:
            tables.append({
                "tableId": table_counter,
                "label": "普通桌",
                "playerIds": ids,
                "submitted": False,
                "results": [],
            })
            table_counter += 1
            record_pair_history(ids)

    STATE["rounds"].append({
        "stage": stage,
        "roundNumber": STATE["currentRound"],
        "tables": tables,
    })
    return jsonify({"ok": True})


def current_round_object():
    """返回当前阶段/当前轮次对应的轮次对象,不管是否已全部提交"""
    if not STATE["rounds"]:
        return None
    last = STATE["rounds"][-1]
    if last["stage"] != STATE["stage"] or last["roundNumber"] != STATE["currentRound"]:
        return None
    return last


def _submit_table(rnd, table, game_points_map):
    """game_points_map: {playerId: gamePoint}"""
    pairs = [(pid, game_points_map[pid]) for pid in table["playerIds"]]
    tp_map = compute_table_points(pairs)
    results = []
    for pid, gp in pairs:
        results.append({"playerId": pid, "gamePoint": gp, "tablePoint": tp_map[pid]})
    results.sort(key=lambda r: -r["gamePoint"])
    table["results"] = results
    table["submitted"] = True


@app.route("/api/table/submit", methods=["POST"])
def api_table_submit():
    """单桌独立提交成绩,不需要等其他桌一起提交"""
    rnd = current_round_object()
    if rnd is None:
        return jsonify({"error": "当前没有正在进行的轮次"}), 400

    data = request.get_json(force=True)
    table_id = data.get("tableId")
    table = next((t for t in rnd["tables"] if t["tableId"] == table_id), None)
    if table is None:
        return jsonify({"error": f"找不到桌次 {table_id}"}), 400

    gp_map = {}
    for r in data.get("results", []):
        gp_map[int(r["playerId"])] = float(r["gamePoint"])
    if set(gp_map.keys()) != set(table["playerIds"]):
        return jsonify({"error": "选手成绩不完整"}), 400

    _submit_table(rnd, table, gp_map)
    return jsonify({"ok": True, "table": {
        "tableId": table["tableId"],
        "results": table["results"],
    }})


@app.route("/api/round/dryrun", methods=["POST"])
def api_round_dryrun():
    """一键随机填充当前轮次所有桌次的成绩并直接提交(测试用)"""
    rnd = current_unsubmitted_round()
    if rnd is None:
        return jsonify({"error": "当前没有待提交的轮次"}), 400

    for table in rnd["tables"]:
        ids = table["playerIds"]
        scores = [random.randint(-800, 1200) for _ in range(len(ids) - 1)]
        scores.append(-sum(scores))  # 保证四家分数总和为 0(零和)
        random.shuffle(scores)
        gp_map = {pid: float(s) for pid, s in zip(ids, scores)}
        _submit_table(rnd, table, gp_map)

    return jsonify({"ok": True})


# ---------------------------------------------------------------------------
# API - 阶段推进
# ---------------------------------------------------------------------------

@app.route("/api/stage/advance", methods=["POST"])
def api_stage_advance():
    stage = STATE["stage"]
    max_rounds = STATE["config"].get(stage + "Rounds") if stage in ("preliminary", "semifinal", "final") else None

    if stage == "preliminary":
        if STATE["currentRound"] < max_rounds:
            return jsonify({"error": "预赛轮次还没打完"}), 400
        standings = standings_for_stage("preliminary")
        # standings 已经排除了 bye 选手
        top8 = [r["playerId"] for r in standings[:8]]
        STATE["qualifiers"] = top8
        # 种子分桌:1,4,5,8 一桌;2,3,6,7 一桌
        seed_a = [top8[0], top8[3], top8[4], top8[7]]
        seed_b = [top8[1], top8[2], top8[5], top8[6]]
        STATE["semifinalTables"]["A"] = seed_a
        STATE["semifinalTables"]["B"] = seed_b
        STATE["stage"] = "semifinal"
        STATE["currentRound"] = 0
        return jsonify({"ok": True, "qualifiers": [player_name(p) for p in top8]})

    if stage == "semifinal":
        if STATE["currentRound"] < max_rounds:
            return jsonify({"error": "半决赛轮次还没打完"}), 400
        champion = []
        consolation = []
        for key in ("A", "B"):
            ids = STATE["semifinalTables"][key]
            rows = standings_for_stage("semifinal", ids)
            champion.extend([r["playerId"] for r in rows[:2]])
            consolation.extend([r["playerId"] for r in rows[2:]])
        STATE["finalTables"]["champion"] = champion
        STATE["finalTables"]["consolation"] = consolation
        STATE["stage"] = "final"
        STATE["currentRound"] = 0
        return jsonify({
            "ok": True,
            "champion": [player_name(p) for p in champion],
            "consolation": [player_name(p) for p in consolation],
        })

    if stage == "final":
        if STATE["currentRound"] < max_rounds:
            return jsonify({"error": "决赛轮次还没打完"}), 400
        champ_rows = standings_for_stage("final", STATE["finalTables"]["champion"])
        consol_rows = standings_for_stage("final", STATE["finalTables"]["consolation"])
        top8_ids = [r["playerId"] for r in champ_rows] + [r["playerId"] for r in consol_rows]

        # 9 名及以后:陪打选手按预赛+半决赛+决赛全程累计 Table Point(Game Point 为 Tie Break)排名
        rest_ids = [pid for pid in STATE["players"] if pid not in top8_ids]
        rest_rows = standings_multi(["preliminary", "semifinal", "final"], rest_ids)
        rest_ranked_ids = [r["playerId"] for r in rest_rows]

        final_ranking = top8_ids + rest_ranked_ids
        STATE["finalRanking"] = final_ranking
        STATE["stage"] = "finished"
        return jsonify({"ok": True, "finalRanking": [player_name(p) for p in final_ranking]})

    return jsonify({"error": "当前阶段无法推进"}), 400


@app.route("/api/pairing-matrix")
def api_pairing_matrix():
    """返回预赛阶段的两两同桌次数矩阵，只含非 bye 选手。"""
    # 只统计 active / drop 选手（排除 bye）
    player_list = [
        {"id": pid, "name": p["name"], "status": p.get("status", "active")}
        for pid, p in STATE["players"].items()
        if p.get("status", "active") != "bye"
    ]
    ids = [p["id"] for p in player_list]

    # 从 rounds 里统计 preliminary 阶段的同桌次数
    counts = {pid: {pid2: 0 for pid2 in ids} for pid in ids}
    for rnd in STATE["rounds"]:
        if rnd["stage"] != "preliminary":
            continue
        for table in rnd["tables"]:
            seated = [p for p in table["playerIds"] if p in counts]
            for i in range(len(seated)):
                for j in range(i + 1, len(seated)):
                    a, b = seated[i], seated[j]
                    counts[a][b] += 1
                    counts[b][a] += 1

    return jsonify({
        "players": player_list,
        "matrix": [[counts[a][b] for b in ids] for a in ids],
    })


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5050, debug=False)
