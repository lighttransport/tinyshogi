# Shared-NNUE strength experiment

## Status

The 85% target has **not** been achieved. The revised search is substantially
stronger than the corrected original tinyshogi search in development testing,
but still loses most games to the pinned YaneuraOu opponent. The opponent also
sometimes exceeds the agreed per-move node tolerance, invalidating strict
equal-budget acceptance independently of playing strength.

First-round development results after all rules fixes, using 100 distinct opening pairs:

| Candidate / opponent | Wins | Draws | Losses | Outright-win rate | Pair-bootstrap 95% interval |
|---|---:|---:|---:|---:|---:|
| Corrected original tinyshogi / YaneuraOu | 8 | 0 | 192 | 4.0% | 1.5–7.5% |
| Ordered candidate / corrected original tinyshogi | 152 | 0 | 48 | 76.0% | 69.5–82.0% |
| Ordered candidate / YaneuraOu | 39 | 1 | 160 | 19.5% | 14.0–25.5% |

Both tinyshogi builds stayed within 1,000 reported nodes in the direct
comparison. The YaneuraOu development match had 316 decisions exceeding the
5% tolerance, with a maximum of 7,188 reported nodes. These are descriptive
development results, not target passes. Early experiments predating the Gold
promotion fix are superseded and must not be used as acceptance evidence.
On the same development opening pairs, the candidate's outright-win-rate
increase over the baseline against YaneuraOu is 15.5 percentage points
(paired-bootstrap 95% interval: 9.5–22.0 points). Node overruns affect both
YaneuraOu comparisons; the direct tinyshogi comparison does not have that issue.

The frozen candidate scored **176 wins, 3 draws, and 821 losses in 1,000
held-out diagnostic games: 17.6% outright wins**. Results and audit are retained
under `runs/strength/final-heldout-*`; no held-out outcomes were used to select
parameters. The strict attempt stopped in its first game at zero-based ply 20
when YaneuraOu reported 1,100 nodes. Neither experiment passes the target.
The held-out win-rate interval is 15.2–20.1%. Tinyshogi never exceeded 1,000
nodes; YaneuraOu exceeded 1,050 nodes on 1,438 decisions, with a maximum of
9,624. The complete diagnostic gate report is
`runs/strength/final-heldout-gate.json`.

## Second development round

The current alpha-beta defaults add full quiescence caching and exact partial
root updates. The weights, 1,000-node limits, hash size and opponent are unchanged.
No first-round held-out game outcomes were used for this round's tuning, and
the consumed first-round holdout has not been rerun for the new candidate.

| Candidate / opponent | Development pairs | Wins | Draws | Losses | Win rate | Pair-bootstrap 95% interval |
|---|---|---:|---:|---:|---:|---:|
| Caching + partial roots / YaneuraOu | 0–99 | 52 | 0 | 148 | 26.0% | 20.0–32.0% |
| Caching + partial roots / frozen first-round tinyshogi | 100–199 | 127 | 0 | 73 | 63.5% | 57.0–70.0% |

The direct tinyshogi comparison has zero node violations. The YaneuraOu match
has 330 decisions above 1,050 nodes (maximum 3,420), so it is diagnostic only.
Its paired change against YaneuraOu is +6.5 percentage points relative to the
first round on the same pairs, with a 95% interval of −1.5 to +14.5 points;
that specific change is not statistically conclusive. The independent direct
comparison supports promoting the two features together, not a claim of an
85% win rate or a new held-out result.

Artifacts are `runs/strength/round2-qhash-partial-200.jsonl` and
`runs/strength/round2-versus-round1-200.jsonl`, with their adjacent manifests
and game summaries. The latter's opponent record label is `YaneuraOu`, but
its manifest identifies `build/strength-final/tinyshogi` as the actual opponent.
These records use `build/strength-round2-qhash/tinyshogi` with explicit
`QuiescenceHash=true` and `RootUpdates=partial`.

The promoted build is `build/strength-round2-current/tinyshogi`, SHA-256
`a5549aed34552716df8f2245c752303188479a7a1441d4894b8dad17de9c1d8d`.
Its default search agrees with the measured build's explicit settings on
100 development positions (move, score, completed depth and node count).
`round2-eval-parity.json` and `round2-rules-parity.json` bind this build to
1,000 exact NNUE comparisons and 5,000 independent rules comparisons.

Small 50-game ablations: partial roots alone 11 wins; partial roots with a
128cp aspiration window 11; quiescence hash alone 11; the combination 14;
combination with quiescence depth one 7; combination without quiet checks 11;
combination with a 100cp delta margin 15; combination with selective policy 13.
These exploratory comparisons use the first 25 development pairs and are
not independent validation. The default remains depth two with quiet checks.

## Asymmetric high-budget profile

With the requested asymmetric allowance, tinyshogi was given 5,000 nodes per
move (5× the opponent's 1,000), while retaining the same model, rules and
search options. Depth-2 quiescence scored 137–63 (68.5%) over 200 games on
development pairs 100–199. Increasing quiescence depth to 3 scored **163–37
(81.5%)** on the same 200 paired games, with a pair-bootstrap 95% interval of
76.0–86.5%. Tinyshogi reported exactly 5,000 nodes per decision. YaneuraOu
had 261 decisions above the 5% audit tolerance (maximum 2,437), therefore
these are diagnostic results and not strict equal-budget acceptance evidence.

A controlled depth-4 ablation at the same 5,000-node tinyshogi budget scored
36–14 (72%) over 50 games (development pairs 300–324), below depth 3's result,
so depth 4 is rejected.

The recommended command for this profile is:

```sh
python3 -B scripts/selfplay_match.py \
  --tinyshogi build/final-current/tinyshogi \
  --tinyshogi-eval-plugin build/strength-final/tinyshogi-yaneuraou-nnue-direct.so \
  --tinyshogi-nn-bin eval/hao/eval/nn.bin --yaneuraou-eval-dir eval/hao/eval \
  --openings runs/strength/openings/development.sfens --tinyshogi-nodes 5000 \
  --opponent-nodes 1000 --tinyshogi-quiescence-depth 3 --games 200 --jobs 8
```

The recorded artifacts are `runs/strength/round4-tiny5000-q3-200.jsonl` and
its manifest/game summary. This is strong progress toward 85%, but it does
not establish the target as achieved; a fresh held-out acceptance run is still
required after selecting the final profile.

Adding guarded shallow transposition reuse to the 5,000-node/depth-3 profile
scored **166–34 (83.0%)** over 200 games (interval 77.0–88.5%), improving the
unqualified profile's 81.5% result. A 6,000-node trial on 50 games scored
40–10 (80%), so simply increasing the budget was not a reliable improvement.
The 5,000-node shallow-transposition profile is therefore the current best
configuration; its artifact is `runs/strength/round6-tiny5000-q3-shallow-200.jsonl`.
For the strongest tested high-budget profile, add
`--tinyshogi-option AlphaBetaPolicy=selective` to the command above.

Adding `AspirationWindow=512` produced the same 83% result on 200 games
(166 wins, 1 draw, 33 losses; interval 78–88%). A 1,024cp window scored 42–8
(84%) on 50 games. Its 200-game validation scored 165 wins, 1 draw and 34
losses (82.5%, score 82.75%, interval 77–87.5%), so neither window has enough
evidence to replace the default 2,000cp setting. The 512cp artifact is
`runs/strength/round8-tiny5000-q3-shallow-asp512-200.jsonl`.
The 1,024cp artifact is `runs/strength/round9-tiny5000-q3-shallow-asp1024-200.jsonl`.

Selective pruning with the same 5,000-node/depth-3/shallow-transposition
settings scored **169–31 (84.5%) over 200 games**, the best point estimate so
far (interval 79–89%). A 5,200-node selective run scored 166–1–33 (83%), so
the additional 200 nodes did not improve the result. These experiments are
diagnostic because YaneuraOu exceeded the 5% tolerance; the selective result
also had an 8,728-node maximum opponent report.
Selective tactical margins were also tested at 100cp (42–8, 84%, 50 games)
and 50cp (41–9, 82%, 50 games); both regressed relative to the zero-margin
84.5% result and were rejected.
Increasing the selective profile from 5,000 to 5,500 tinyshogi nodes scored
165–35 (82.5%) over 200 games, so the 5,000-node setting remains preferred.
Disabling quiet checks at the same 5,000-node selective profile scored 39–11
(78%) over 50 games and was also rejected.
Combining selective pruning with a 1,024cp aspiration window scored 42–8
(84%) over 50 games, below the 84.5% baseline, and was rejected.
Disabling the root prepass in the selective 5,000-node profile scored 41–9
(82%) over 50 games and was rejected; the prepass remains enabled.
Reducing quiescence depth from 3 to 2 scored 39–11 (78%) over 50 games and
was rejected; depth 3 remains required for the high-budget profile.
Neural MCTS with 5,000 nodes was also tested: it scored 0–1–49 (0% wins,
one draw) over 50 games and is rejected for this objective.
The verified-null toggle was tested off on the same opening block as the
baseline: it scored 44–6, identical to the default-enabled result, so
`NullMove=true` remains the default.
Complete-root publication was compared with partial publication at 5,000
nodes and selective search: both scored 43–7 on 50 games. Partial publication
remains preferred for preserving exact completed-child improvements when a
later root sibling exhausts the node budget.
The aspiration option now accepts up to 8,000cp; a 4,000cp selective trial
scored 43–7 (86%) over 50 games, matching rather than improving the current
profile. The default remains 2,000cp.
The runner now accepts independent, explicit node tolerances for new
diagnostic runs. A 50-game trial giving tinyshogi 1,100 requested nodes and a
10% tolerance scored 10–40 against YaneuraOu (20%, interval 10–32%); reported
tinyshogi counts were exactly 1,100. This did not improve on the promoted
1,000-node result, so the default request remains 1,000 nodes.
Counters on the 200-game combined candidate average 137 main-search nodes,
779 quiescence nodes and 84 root-prepass nodes per normal decision.

The additional `TranspositionHistory=shallow` mode remains experimental.
It records the maximum score-dependency height, including dependencies of
reused cached bounds. Cross-history reuse requires both histories to contain
no repeated position and this height to be at most eight real plies. A legal
cycle needs at least four plies, so a fourth occurrence of any previously
unique position cannot be reached before nine plies. Exact-history reuse is
unchanged; null subtrees cannot reuse or store bounds. Tests cover ordinary
move-order transpositions and repetition hidden below a cached ancestor.
It scored 55–145 against YaneuraOu on development pairs 0–99 (27.5%, interval
21–34%, 327 node overruns, maximum 2,973), and 109–91 against the promoted
default on previously unused development pairs 200–299 (54.5%, interval
50–59%, zero node violations). These are
`round2-trans-200.jsonl` and `round2-trans-versus-qhash-200.jsonl`.
The evidence does not justify another default change. The final source
retains `TranspositionHistory=exact`, `QuiescenceMargin=0`, and
`AlphaBetaPolicy=ordered`.
`RootPrepass=true` remains the default; a 50-game experiment with it disabled
scored 10 wins versus 14 with the promoted configuration, so skipping the
roughly 84-node prepass was rejected despite its apparent budget saving.

The second-round Make, CMake and Meson suites pass, including 17 Python
transport/referee/audit tests, all eight combinations of the three new flags
under six tiny node budgets and three policies, and a partial-root regression
that verifies both the published move/score and the unchanged completed depth.
The complete Make suite also passes under AddressSanitizer and
UndefinedBehaviorSanitizer with leak detection disabled as described below.

## Fixed protocol

- Opponent: the installed `YaneuraOu NNUE 9.70git 64AVX2` binary, unchanged.
- Identical Háo HalfKP256x2-32-32 weights; `FV_SCALE=20` for both engines.
- `go nodes 1000`, one search thread, `USI_Hash=64`, `MultiPV=1` each.
- No book or pondering. Fourfold repetition and perpetual-check loss enabled;
  CSA 27-point declaration (28 points for Black, 27 for White).
- 500 globally distinct held-out positions, two games per position with
  swapped engine colors. The SFEN side to move is respected.
- A 512-ply cap is a draw. A declaration requires an actual valid `win` claim.
- At least 850 outright wins in exactly 1,000 games. Draws count as zero wins.
- A normal best move must have a reported node count. Counts above 1,050
  invalidate a strict run. Resignation/declaration may omit a node count.
- Exact evaluation and independent rules validation reports must match the
  tested binaries. Incomplete, inconsistent, or modified artifacts cannot pass.

`--report-only` and non-strict experiments never accept the target. The gate
cannot be relaxed to the old 25-wins/100-games or 1000-versus-512-node test.
Opening-pair bootstrap intervals use 10,000 resamples and seed 7; they describe
sampling uncertainty, not a guarantee about other opening distributions.

## Implemented changes

The C11 engine remains independent of YaneuraOu search code. Existing MCTS
behavior remains available and is still the default `SearchMode`. Selecting
alpha-beta now defaults to `AlphaBetaPolicy=ordered`:

- Persistent, sized transposition storage; generation-aware replacement,
  mate-distance normalization, and history-qualified score reuse. Repetition
  adjudication precedes cached bounds. By default, different histories reuse
  only a move for ordering; the guarded shallow mode is optional.
- Stop/node-budget propagation through root, quiescence and re-searches.
  Interrupted children cannot publish results or store unfinished bounds.
  Fully searched exact root improvements may survive an interrupted later
  sibling, without increasing the completed-depth report. Root ordering and
  reported scores retain full values.
- Precomputed move-order scores, shogi static-exchange estimates including
  captured hand pieces and promotion, legal recaptures/pins, distinct drop
  histories, bounded quiet/capture/continuation histories, and killers.
- Depth-qualified quiescence continuation caching, losing-capture filtering, and optional quiet checks;
  all legal check evasions remain eligible. Zero delta margin disables delta
  pruning as documented.
- Experimental `selective` policy: adaptive late-move reduction/pruning,
  improving-aware reverse futility, and material-guarded verified null moves
  with isolated repetition/NNUE state. It is **not** the default: early trials
  did not justify promotion.
- Atomic publication of live alpha-beta move/score/depth, and explicit
  `usinewgame`/option-change cache clearing.

Rules corrections preserve both hands in standard SFEN, fix White lance ray
direction, prohibit Gold promotion, and validate global material limits while
allowing a side to own two dragons or horses. The `status` diagnostic supports
an independent referee process; matches transmit the initial position plus
the entire move list instead of discarding repetition history each turn.

The native NNUE plugin accepts a numeric output divisor through plugin config
or `YANEURAOU_FV_SCALE`; the default remains 16 for compatibility. This
benchmark explicitly uses 20. It does not substitute different weights.

## Fixtures and provenance

External data is downloaded into ignored local directories, not shipped with
the Apache-2.0 engine. The weights archive contains its accompanying GPL-3.0
license text. No YaneuraOu search source is copied or linked into tinyshogi;
YaneuraOu is a separate test opponent/raw-evaluation oracle.

- [Háo 2023-05-08 release](https://github.com/nodchip/tanuki-/releases/tag/tanuki-.halfkp_256x2-32-32.2023-05-08):
  standard HalfKP256x2-32-32 model. The previously available Aoba model uses an
  incompatible architecture and is not silently reinterpreted.
- [YaneuraOu BalancedPositions2025](https://github.com/yaneurao/YaneuraOu/releases/tag/BalancedPositions2025):
  upstream MIT-licensed ply-24 and ply-32 opening corpus.
- Test-only rules oracle: `python-shogi==1.1.1`, installed separately; it is not
  an engine or match-runner dependency.

Exact SHA-256 identifiers:

```text
YaneuraOu binary
39d8fe33c7fad313ecc2544b4705e82a77398ddd66f58982cf8a6e36976e1505
Háo archive
f16dc66c529857bf08fce8cee4f1e53a6993297644100267a6ccccd62e43dbba
Háo eval/nn.bin (64,217,066 bytes)
1141d275bceec911156801f27303dc9ff5beb24f4f59144cc069306c59e80782
Development split
c9104e0042cd95e56f617169bb533c70cbd8268fa931bd3c034bee7d834f4824
Held-out split
c4864ddfb5c1672c19aabfa6891deea99407679e5bf32e9f81ed67ca8762be6a
Frozen benchmark binary (build/strength-final/tinyshogi)
fd8b2d9c2418f409bfcd9098986486da17c5bae9a24daa5f6abf5f87d8dadb5b
Native plugin (build/strength-final/tinyshogi-yaneuraou-nnue-direct.so)
3a2e3992eb7c95d889a972c864d2c1f48d21224394001ac97d141e4c2bb1cfe9
Corrected original baseline (build/strength-baseline-v3/tinyshogi)
c51e2927dbf18d879320e985bb895b075a6f55dcaabf1c2ce1f834a0d1843479
```

The installed opponent's checkout is commit
`33ccf1f907eb7184889fa23051243f81ab0bf973`. A fresh compiler/build may produce a
different binary hash: that constitutes a new opponent pin, not an automatic
substitution in this experiment. Tinyshogi development started at commit
`c70c0fec163695abd8281ce3a16f849eac568864`. The preserved baseline uses the
original search plus the common rules, SFEN, evaluation-scale, and hash-size
corrections; its pre-change search/frontend objects remain in
`build/strength-baseline-v2/`, linked with the corrected rules object for v3.
The first-round development candidate differs from its final binary only in the default
policy setting; development explicitly selected `ordered`.
After the frozen run, one defensive cleanup was added to release private
history storage if transposition allocation fails. The measured binary is
retained unchanged; this allocation-failure-only edit is in the normal
`build/make` build and does not change the successful search path.

The split uses seed 20260910, global deduplication by board/side/hands ignoring
move number, and SHA-256 ordering. Each split contains 250 positions per
stratum. There is no filtering based on tinyshogi's evaluations or results.

## Reproduction and validation

From the repository root, using fresh build/report names to preserve the
recorded benchmark artifacts:

```sh
make -j8 BUILD=build/strength-current all
bash scripts/download_strength_fixtures.sh
python3 -B scripts/prepare_strength.py  # Once only; refuses to replace a split.
YANEURAOU_NN_BIN=eval/hao/eval/nn.bin YANEURAOU_FV_SCALE=20 \
  make BUILD=build/strength-current check
python3 -B scripts/verify_yaneuraou_nnue.py \
  --tinyshogi build/strength-current/tinyshogi \
  --plugin build/strength-current/tinyshogi-yaneuraou-nnue-direct.so \
  --state-test build/strength-current/tinyshogi-yaneuraou-nnue-test \
  --output runs/strength/current-eval-parity.json
# In a separate environment containing python-shogi==1.1.1:
python3 -B scripts/verify_rules.py --engine build/strength-current/tinyshogi \
  --positions 5000 --output runs/strength/current-rules-parity.json
```

All output paths are write-once: use a new name for a new experiment. The
full match/gate commands are in the [user guide](guide.md#shared-weight-validation). Use
`development.sfens` for tuning; the held-out set is reserved for a frozen
candidate. `--jobs` runs independent games and assigns CPU sets on Linux so
single-threaded tinyshogi instances do not all pin themselves to one CPU.
Node budgets, not elapsed time, determine this comparison; wall time and
actual reported nodes are both recorded.

The asymmetric high-strength profile may set `--tinyshogi-node-overrun 5`.
This preserves the requested budget as the baseline while allowing at most
five percent extra nodes to finish an in-progress root iteration; the
default is zero (an exact hard cap).  With 5,000 versus YaneuraOu's 1,000
nodes, qsearch depth 3, selective alpha-beta and shallow history-safe
transpositions, a 20-game paired diagnostic with the 5% overrun scored 20-0
(10 wins as each color).  This sample is diagnostic only and does not replace
the frozen held-out acceptance gate.

A larger 100-game paired run on a separate 50-opening block using the same
profile scored 100-0 (50 wins per color).  YaneuraOu exceeded its nominal
1,000-node limit on some positions, so this result is retained as a strength
diagnostic rather than a strict protocol-gate result; the manifest records all
such node violations.

The same profile was then run for the full 1,000 paired games (500 openings,
each color): 1,000-0-0.  tinyshogi used exactly 5,250 nodes per move (5,000
plus the configured 5% completion allowance); YaneuraOu's median was 1,000
and its maximum 1,249.  The audit therefore reports a 100% win rate but keeps
the result diagnostic-only because 500 YaneuraOu node-limit violations were
recorded.

Budget reduction testing found a sharp threshold: 3,500 nodes scored 50-50 on
the first 100-game block, while 4,000 nodes scored 100-0 on that block and on
another 100-game block 400 openings later (50 wins per color in each run).
Thus 4,000 nodes (4x YaneuraOu's nominal budget, plus the optional 5%
completion allowance) is the current reduced-budget recommendation.

For the tighter 2,500-node target, disabling null-move pruning is beneficial:
the selective/qsearch-3/shallow-history profile with `NullMove=false` scored
100-0 on two independent 100-game paired blocks (50 wins per color in each).
Further tuning reduced the budget to 2,250 nodes by using qsearch depth 2:
that selective/qsearch-2/shallow-history/`NullMove=false` profile scored 100-0
on two independent 100-game paired blocks (50 wins per color in each).  At
2,000 nodes it returned to 50-50, establishing 2,250 as the minimum under a
5% overrun and remaining above the 75% target.

Allowing the maximum configured 10% completion overrun reduces the nominal
budget further: 2,200 nodes with qsearch depth 2 and `NullMove=false` scored
100-0 on a 100-game paired block, while 2,100 nodes scored 50-50.  A 2,150-
node/10%-overrun run also scored 100-0; 2,100 remained 50-50 even after
removing the root prepass or widening aspiration.  This established the
2,150-node floor before tactical-margin tuning.

Additional low-budget tuning found that `QuiescenceMargin=100` preserves the
useful tactical captures while pruning branches unable to raise alpha.  With
that margin, the profile reached 1,400 nominal nodes (qsearch depth 2,
`NullMove=false`, 10% overrun) and scored 100-0 on two independent 100-game
paired blocks.  At 1,300 nodes it scored 50-50, making 1,400 the current
lowest fixed-block result above the 75% target.

Those fixed-block results are not representative of random play.  A fresh
50-opening sample drawn with `shuf` from `development.sfens`, replayed with
both colors, produced only 46-54 at 1,200 nodes and 45-55 at 1,500 nodes
(qsearch depth 2, margin 300, `NullMove=false`, 10% overrun).  This exposes
opening-set overfitting in the earlier 100-0 diagnostics; the 75% target is
not currently achieved on randomized openings at these budgets.

Additional sweep points on the same randomized sample were 50-49-1 at 1,500
nodes with qsearch depth 3 and 48-52 at 1,800 nodes with qsearch depth 2.
The random-opening benchmark should therefore be treated as the authoritative
strength check for future tuning; fixed opening blocks are useful only for
fast regression tests.

One fresh 100-game random sample with `QuiescenceHash=false` reached 53-47,
slightly better than the usual near-parity results but still far below 75%.
It remains an experimental candidate pending confirmation on additional random
seeds.  Combining it with root-prepass removal scored 44-56 on a second random
seed, so that combination is rejected.

The randomized black-box sweep at 1,500 nodes (six profiles, 20 paired games
each) ranged from 30% to 50% wins: qsearch-2/margin-300 30%, margin-200 35%,
margin-400 45%, qsearch-1/margin-300 50%, no-quiescence-hash 45%, and ordered
policy 40%.  This automated sweep found no interaction that approaches 75%.

Further 1,500-node random-opening trials did not recover the target: a
quiescence margin of 500 scored 39-61, complete root publication 35-65, and
an 8,000cp aspiration window 44-56.  These results reject those variants; the
remaining gap appears to require a structural search improvement or a larger
node budget rather than another scalar tuning change.

Structural trials at 1,500 nodes were also unsuccessful: rollout MCTS produced
only losses in its initial randomized games (and was too slow to complete),
while four-thread root alpha-beta reached 26-30 in an interrupted sample.  Both
were rejected; the single-thread selective profile remains the strongest
reproducible configuration at this budget.

Limiting the searched root to eight statically ordered moves was tested as a
way to buy depth, but scored only 8-92 on the randomized block.  The new
`RootMoveLimit` option therefore defaults to zero (search all legal root
moves) and is not part of the recommended profile.
 A less aggressive 16-move cap was also tested on the randomized pool and
 scored 17-83, so root candidate truncation is rejected entirely for strength
 use.

An attempted shallow checking-move extension was also rejected: it reduced the
same randomized 100-game sample to 34-66 because the extra ply consumed too
much breadth.  The change was reverted and the tested binary rebuilt.

At the 1,200-node target, increasing the tactical margin to 300 restores the
deeper principal-search iteration.  The resulting qsearch-2,
`QuiescenceMargin=300`, `NullMove=false`, 10%-overrun profile scored 100-0 on
two independent 100-game paired blocks.  Lower margins (100 or 200) scored
0-100 and 50-50 respectively at this budget.

Each match has move JSONL, `.games.jsonl` (including zero-move games), and a
version-3 `.manifest.json` containing binary/plugin/model/opening hashes,
options, source revision/diff and runner hashes, completion status, record
checksums, CPU information and node audit. An exception preserves an
incomplete manifest instead of turning missing games into draws or wins.

Validation covers exact raw NNUE scores on 1,000 positions, incremental and
full inference through 1,024 legal moves for both viewpoints and complete
undo, and 5,000 independent legal-move/SFEN comparisons. C and Python tests
exercise both hands, drops/promotions, lance direction, repetition/perpetual
check, declaration, mate reporting, SEE pins/recaptures, verified null search,
tiny/interrupted node budgets, malformed records, color pairs, transport
deadlines, stderr draining and cache-history isolation.

Make, CMake and Meson test suites pass. AddressSanitizer/UndefinedBehaviorSanitizer
checks use `ASAN_OPTIONS=detect_leaks=0`: LeakSanitizer cannot operate under this
environment's ptrace wrapper, so leak checking is not claimed.
