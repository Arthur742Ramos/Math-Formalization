/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license.
-/
module
public import ErdosOverlap.Certificate.CoarseNative6

/-! Exact finite cover for the source-bound stronger certificate. -/
namespace ErdosOverlap.Certificate.FrontierCover
@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def height : ℚ := (380627990701/1000000000000 : ℚ)

def denominatorBound : ℚ := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)
def centralIntegralLower : ℚ := (9279416483850940695419264776456365460731/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower04 : ℚ := (7392528366906978082743047144045720929481/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower05 : ℚ := (6960805450460979869048596590513982648231/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower06 : ℚ := (3116621162932609217356296878177279410053/41538374868278621028243970633760768000000000000 : ℚ)
def profileIntegralLower07 : ℚ := (5664016548380297935411173049810369366981/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower08 : ℚ := (2500724586747284470649870170219271597553/41538374868278621028243970633760768000000000000 : ℚ)
def profileIntegralLower09 : ℚ := (1345785034738702885081446826978060660053/41538374868278621028243970633760768000000000000 : ℚ)
def profileIntegralLower10 : ℚ := (4638687464304541675880236337995638785053/41538374868278621028243970633760768000000000000 : ℚ)
def profileIntegralLower11 : ℚ := (9278050542755840798455437971005193585731/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower12 : ℚ := (9277776490588435849130574954739568585731/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower13 : ℚ := (9275487208321162604159218114777654523231/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower14 : ℚ := (9277933560187140834146531287673162335731/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower15 : ℚ := (4638931663767601982063573693050814566303/41538374868278621028243970633760768000000000000 : ℚ)
def profileIntegralLower16 : ℚ := (289931823764940685929427206385515387933/2596148429267413814265248164610048000000000000 : ℚ)
def profileIntegralLower17 : ℚ := (9277833525621905629172101913358709210731/83076749736557242056487941267521536000000000000 : ℚ)
def profileIntegralLower18 : ℚ := (4638924206835465460343134237789584097553/41538374868278621028243970633760768000000000000 : ℚ)
def profileIntegralLower19 : ℚ := (9277903002986107865833848497499822491981/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: central. -/
def native00 : Row where
  lo := 0
  hi := (50734931/500000000000 : ℚ)
  a := (2076918975399322378498281777859143689423819637891/2076918743413931051412198531688038400000000000000 : ℚ)
  b := 0
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile11. -/
def native01 : Row where
  lo := (50734931/500000000000 : ℚ)
  hi := (170916973/1000000000000 : ℚ)
  a := (20282411509209769680590526430473588932087832553868474163/20282409603651670423947251286016000000000000000000000000 : ℚ)
  b := (174759880435807/1000000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile14. -/
def native02 : Row where
  lo := (170916973/1000000000000 : ℚ)
  hi := (36887909/200000000000 : ℚ)
  a := (4056482260976943892504847613915652966985771697730481351/4056481920730334084789450257203200000000000000000000000 : ℚ)
  b := (23369748718369/100000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile19. -/
def native03 : Row where
  lo := (36887909/200000000000 : ℚ)
  hi := (303113/1600000000 : ℚ)
  a := (20282411254152580536708215017393211526975878018702652253/20282409603651670423947251286016000000000000000000000000 : ℚ)
  b := (247258610695001/1000000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile15. -/
def native04 : Row where
  lo := (303113/1600000000 : ℚ)
  hi := (4820299/25000000000 : ℚ)
  a := (10141205600529708251515617487480222575628562051412617039/10141204801825835211973625643008000000000000000000000000 : ℚ)
  b := (4079304191633/15625000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile18. -/
def native05 : Row where
  lo := (4820299/25000000000 : ℚ)
  hi := (97255451/500000000000 : ℚ)
  a := (2028241118284772009065145525946648623261962138324621741/2028240960365167042394725128601600000000000000000000000 : ℚ)
  b := (265732043537707/1000000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile17. -/
def native06 : Row where
  lo := (97255451/500000000000 : ℚ)
  hi := (196217151/1000000000000 : ℚ)
  a := (20282411164380981372990779517618361720056053439628586459/20282409603651670423947251286016000000000000000000000000 : ℚ)
  b := (270412621368237/1000000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile16. -/
def native07 : Row where
  lo := (196217151/1000000000000 : ℚ)
  hi := (199662077/1000000000000 : ℚ)
  a := (633825348301682015489609316907457768301607903599953709/633825300114114700748351602688000000000000000000000000 : ℚ)
  b := (34389742376329/125000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile12. -/
def native08 : Row where
  lo := (199662077/1000000000000 : ℚ)
  hi := (222291711/1000000000000 : ℚ)
  a := (1298074309622810478122627408929091403010542185202459/1298074214633706907132624082305024000000000000000000 : ℚ)
  b := (1808685929653/6250000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile10. -/
def native09 : Row where
  lo := (222291711/1000000000000 : ℚ)
  hi := (19276249/62500000000 : ℚ)
  a := (10141205289757603076953710660400671163696298050157342509/10141204801825835211973625643008000000000000000000000000 : ℚ)
  b := (16085451792097/40000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile13. -/
def native10 : Row where
  lo := (19276249/62500000000 : ℚ)
  hi := (518263447/1000000000000 : ℚ)
  a := (20282408275848280904933314774789507539113890510278596879/20282409603651670423947251286016000000000000000000000000 : ℚ)
  b := (77038848279067/100000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile04. -/
def native11 : Row where
  lo := (518263447/1000000000000 : ℚ)
  hi := (53905423/100000000000 : ℚ)
  a := (1298073991821182448166207682523253008043067169345553/1298074214633706907132624082305024000000000000000000 : ℚ)
  b := (975280539551279/1000000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile05. -/
def native12 : Row where
  lo := (53905423/100000000000 : ℚ)
  hi := (75882227/100000000000 : ℚ)
  a := (1298073734320656245172930157912859637836626879969247/1298074214633706907132624082305024000000000000000000 : ℚ)
  b := (1343276768028649/1000000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile06. -/
def native13 : Row where
  lo := (75882227/100000000000 : ℚ)
  hi := (1060353981/1000000000000 : ℚ)
  a := (649036518217925271727869047684385482564815448747181/649037107316853453566312041152512000000000000000000 : ℚ)
  b := (1025889708748977/500000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile07. -/
def native14 : Row where
  lo := (1060353981/1000000000000 : ℚ)
  hi := (682625293/500000000000 : ℚ)
  a := (1298072238775862548762160619666434300388052108581613/1298074214633706907132624082305024000000000000000000 : ℚ)
  b := (1315647335475141/500000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile08. -/
def native15 : Row where
  lo := (682625293/500000000000 : ℚ)
  hi := (470455089/250000000000 : ℚ)
  a := (5192285107647172284776114298327720121150186909357/5192296858534827628530496329220096000000000000000 : ℚ)
  b := (1587023206272491/500000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

/-- Source witness: profile09. -/
def native16 : Row where
  lo := (470455089/250000000000 : ℚ)
  hi := (9/2560 : ℚ)
  a := (649034034572674278580514948562098028446615940798717/649037107316853453566312041152512000000000000000000 : ℚ)
  b := (224361288180009/50000000000000000 : ℚ)
  c := (-13740060377814761164847080968941279479896018207304341625412297/20000000000000000000000000000000000000000000000000000000000000 : ℚ)
  d := (218262346315091146845978870307338706322864781663/83076749736557242056487941267521536000000000000 : ℚ)

def nativeRows : List Row := [native00, native01, native02, native03, native04, native05, native06, native07, native08, native09, native10, native11, native12, native13, native14, native15, native16]

def positiveRows : List Row := nativeRows ++ CoarseNative6.outerRows

theorem positiveRows_valid : ∀ r ∈ positiveRows, r.Valid height := by
  have h : positiveRows.all (fun r => decide (r.Valid height)) = true := by decide +kernel
  intro r hr
  exact of_decide_eq_true ((List.all_eq_true.mp h) r hr)

theorem positiveRows_chain : CoverChain 0 1 positiveRows := by
  exact

    CoverChain.cons native00 (lo := native01.lo) (by decide +kernel) <|

    CoverChain.cons native01 (lo := native02.lo) (by decide +kernel) <|

    CoverChain.cons native02 (lo := native03.lo) (by decide +kernel) <|

    CoverChain.cons native03 (lo := native04.lo) (by decide +kernel) <|

    CoverChain.cons native04 (lo := native05.lo) (by decide +kernel) <|

    CoverChain.cons native05 (lo := native06.lo) (by decide +kernel) <|

    CoverChain.cons native06 (lo := native07.lo) (by decide +kernel) <|

    CoverChain.cons native07 (lo := native08.lo) (by decide +kernel) <|

    CoverChain.cons native08 (lo := native09.lo) (by decide +kernel) <|

    CoverChain.cons native09 (lo := native10.lo) (by decide +kernel) <|

    CoverChain.cons native10 (lo := native11.lo) (by decide +kernel) <|

    CoverChain.cons native11 (lo := native12.lo) (by decide +kernel) <|

    CoverChain.cons native12 (lo := native13.lo) (by decide +kernel) <|

    CoverChain.cons native13 (lo := native14.lo) (by decide +kernel) <|

    CoverChain.cons native14 (lo := native15.lo) (by decide +kernel) <|

    CoverChain.cons native15 (lo := native16.lo) (by decide +kernel) <|

    CoverChain.cons native16 (lo := CoarseNative6.outer114.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer114 (lo := CoarseNative6.outer115.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer115 (lo := CoarseNative6.outer116.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer116 (lo := CoarseNative6.outer117.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer117 (lo := CoarseNative6.outer118.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer118 (lo := CoarseNative6.outer119.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer119 (lo := CoarseNative6.outer120.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer120 (lo := CoarseNative6.outer121.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer121 (lo := CoarseNative6.outer122.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer122 (lo := CoarseNative6.outer123.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer123 (lo := CoarseNative6.outer124.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer124 (lo := CoarseNative6.outer125.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer125 (lo := CoarseNative6.outer126.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer126 (lo := CoarseNative6.outer127.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer127 (lo := CoarseNative6.outer128.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer128 (lo := CoarseNative6.outer129.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer129 (lo := CoarseNative6.outer130.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer130 (lo := CoarseNative6.outer131.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer131 (lo := CoarseNative6.outer132.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer132 (lo := CoarseNative6.outer133.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer133 (lo := CoarseNative6.outer134.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer134 (lo := CoarseNative6.outer135.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer135 (lo := CoarseNative6.outer136.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer136 (lo := CoarseNative6.outer137.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer137 (lo := CoarseNative6.outer138.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer138 (lo := CoarseNative6.outer139.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer139 (lo := CoarseNative6.outer140.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer140 (lo := CoarseNative6.outer141.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer141 (lo := CoarseNative6.outer142.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer142 (lo := CoarseNative6.outer143.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer143 (lo := CoarseNative6.outer144.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer144 (lo := CoarseNative6.outer145.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer145 (lo := CoarseNative6.outer146.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer146 (lo := CoarseNative6.outer147.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer147 (lo := CoarseNative6.outer148.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer148 (lo := CoarseNative6.outer149.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer149 (lo := CoarseNative6.outer150.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer150 (lo := CoarseNative6.outer151.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer151 (lo := CoarseNative6.outer152.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer152 (lo := CoarseNative6.outer153.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer153 (lo := CoarseNative6.outer154.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer154 (lo := CoarseNative6.outer155.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer155 (lo := CoarseNative6.outer156.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer156 (lo := CoarseNative6.outer157.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer157 (lo := CoarseNative6.outer158.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer158 (lo := CoarseNative6.outer159.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer159 (lo := CoarseNative6.outer160.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer160 (lo := CoarseNative6.outer161.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer161 (lo := CoarseNative6.outer162.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer162 (lo := CoarseNative6.outer163.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer163 (lo := CoarseNative6.outer164.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer164 (lo := CoarseNative6.outer165.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer165 (lo := CoarseNative6.outer166.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer166 (lo := CoarseNative6.outer167.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer167 (lo := CoarseNative6.outer168.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer168 (lo := CoarseNative6.outer169.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer169 (lo := CoarseNative6.outer170.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer170 (lo := CoarseNative6.outer171.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer171 (lo := CoarseNative6.outer172.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer172 (lo := CoarseNative6.outer173.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer173 (lo := CoarseNative6.outer174.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer174 (lo := CoarseNative6.outer175.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer175 (lo := CoarseNative6.outer176.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer176 (lo := CoarseNative6.outer177.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer177 (lo := CoarseNative6.outer178.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer178 (lo := CoarseNative6.outer179.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer179 (lo := CoarseNative6.outer180.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer180 (lo := CoarseNative6.outer181.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer181 (lo := CoarseNative6.outer182.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer182 (lo := CoarseNative6.outer183.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer183 (lo := CoarseNative6.outer184.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer184 (lo := CoarseNative6.outer185.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer185 (lo := CoarseNative6.outer186.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer186 (lo := CoarseNative6.outer187.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer187 (lo := CoarseNative6.outer188.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer188 (lo := CoarseNative6.outer189.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer189 (lo := CoarseNative6.outer190.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer190 (lo := CoarseNative6.outer191.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer191 (lo := CoarseNative6.outer192.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer192 (lo := CoarseNative6.outer193.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer193 (lo := CoarseNative6.outer194.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer194 (lo := CoarseNative6.outer195.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer195 (lo := CoarseNative6.outer196.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer196 (lo := CoarseNative6.outer197.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer197 (lo := CoarseNative6.outer198.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer198 (lo := CoarseNative6.outer199.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer199 (lo := CoarseNative6.outer200.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer200 (lo := CoarseNative6.outer201.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer201 (lo := CoarseNative6.outer202.lo) (by decide +kernel) <|

    CoverChain.cons CoarseNative6.outer202 (lo := CoarseNative6.outer203.lo) (by decide +kernel) <|

    CoverChain.single CoarseNative6.outer203

theorem separates_every_nonnegative_mean (m : ℝ) (hlo : 0 ≤ m) (hhi : m ≤ 1) :
    ∃ r ∈ positiveRows, (r.lo : ℝ) ≤ m ∧ m ≤ (r.hi : ℝ) ∧ (height : ℝ) < r.eval m := by
  exact exists_separating_row positiveRows_chain positiveRows_valid m (by simpa using hlo) (by simpa using hhi)

end
end ErdosOverlap.Certificate.FrontierCover
