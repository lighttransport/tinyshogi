/-
  T8: `make_legal_probe`, part 2 — the body, split into named pieces.
-/
import Shogi.C.Proofs.Probe1

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def pb0 : Stmt := (.set 3 (.var 1))
def pb1 : Stmt := (.alloc 1 5)
def pb2 : Stmt := (.memcpy (.var 1) (.var 3) (.const (.int ⟨64, false⟩ 5)))
def pb3 : Stmt := (.set 4 (.load (.int ⟨32, false⟩) (.field (.var 0) 96)))
def pb4 : Stmt := (.memcpy (.field (.var 2) 0) (.var 1) (.const (.int ⟨64, false⟩ 5)))
def pb5 : Stmt := (.store (.int ⟨32, false⟩) (.field (.var 2) 8) (.var 4))
def pb6 : Stmt := (.store (.int ⟨8, false⟩) (.field (.var 2) 13) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))))
def pb7 : Stmt := (.store (.int ⟨8, false⟩) (.field (.var 2) 14) (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.var 4) 1)))
def pb8 : Stmt := (.store (.int ⟨8, false⟩) (.field (.var 2) 15) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 255))))
def pb9 : Stmt := (.store (.int ⟨8, false⟩) (.field (.var 2) 16) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))))
def pb11 : Stmt := (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 1) 1)) 1) (.load (.int ⟨8, false⟩) (.field (.var 2) 12)))
def pb12 : Stmt := (.seq (.call (some 16) 2 [(.load (.int ⟨8, false⟩) (.field (.var 2) 12))]) (.ite (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 16)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))) (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.var 4) 1) (.load (.int ⟨8, false⟩) (.field (.var 1) 1))) .skip))
def pb13 : Stmt := (.store (.int ⟨32, false⟩) (.field (.var 0) 96) (.cast ⟨32, false⟩ (.bin .bxor (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1))))))
def pbCond : Expr := (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 0))) (.const (.int ⟨32, true⟩ 255)))
def pd0 : Stmt := (.set 5 (.bin .sub (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 4))) (.const (.int ⟨32, false⟩ 1))))
def pd1 : Stmt := (.seq (.call (some 6) 0 [(.var 4), (.cast ⟨32, false⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 4)))]) (.store (.int ⟨8, false⟩) (.field (.var 2) 12) (.var 6)))
def pd2 : Stmt := (.store (.int ⟨8, false⟩) (.field (.var 2) 15) (.cast ⟨8, false⟩ (.var 5)))
def pd3 : Stmt := (.store (.int ⟨8, false⟩) (.field (.var 2) 16) (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 5) 1)))
def pd4 : Stmt := (.store (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 5) 1) (.cast ⟨8, false⟩ (.bin .sub (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 5) 1))) (.const (.int ⟨32, true⟩ 1)))))
def pn0 : Stmt := (.set 7 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 1) 0)) 1)))
def pn1 : Stmt := (.set 8 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 1) 1)) 1)))
def pn2 : Stmt := (.store (.int ⟨8, false⟩) (.field (.var 2) 12) (.var 7))
def pn3 : Stmt := (.store (.int ⟨8, false⟩) (.field (.var 2) 13) (.var 8))
def pn4 : Stmt := (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 1) 0)) 1) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))))
def pn5 : Stmt := (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 8)) (.const (.int ⟨32, true⟩ 0))) (.seq (.seq (.call (some 10) 2 [(.var 8)]) (.seq (.call (some 11) 4 [(.var 10)]) (.seq (.call (some 12) 13 [(.var 11)]) (.set 9 (.var 12))))) (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 15) (.cast ⟨8, false⟩ (.var 9))) (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 16) (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 9) 1))) (.store (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 9) 1) (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 9) 1))) (.const (.int ⟨32, true⟩ 1)))))))) .skip)
def pn6 : Stmt := (.ite (.load (.int ⟨8, false⟩) (.field (.var 1) 3)) (.seq (.call (some 13) 2 [(.var 7)]) (.seq (.call (some 14) 6 [(.var 13)]) (.seq (.call (some 15) 0 [(.var 4), (.var 14)]) (.store (.int ⟨8, false⟩) (.field (.var 2) 12) (.var 15))))) .skip)
def pbDrop : Stmt := (.seq pd0 (.seq pd1 (.seq pd2 (.seq pd3 pd4))))
def pbNorm : Stmt := (.seq pn0 (.seq pn1 (.seq pn2 (.seq pn3 (.seq pn4 (.seq pn5 pn6))))))
theorem probe_body_eq : Gen.make_legal_probe.body = (.seq pb0 (.seq pb1 (.seq pb2 (.seq pb3 (.seq pb4 (.seq pb5 (.seq pb6 (.seq pb7 (.seq pb8 (.seq pb9 (.seq (.ite pbCond pbDrop pbNorm) (.seq pb11 (.seq pb12 pb13))))))))))))) := rfl

end Shogi.C.Proofs
