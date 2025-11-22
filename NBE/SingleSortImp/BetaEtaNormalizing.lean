import NBE.SingleSortImp.BetaEta
import NBE.SingleSortImp.Presheaf

namespace SingleSortImp
namespace BetaEtaNormalizing


def NE: Presheaf where
  Pred Γ t T := exists t', t.eq t' ∧ Tm.NE Γ t' T
  weaken {Γ' Γ t T} := by
    rintro ⟨t', E, N⟩
    exists t'.up 0 Γ'.length
    and_intros
    . apply E.up
    . apply N.weaken_app


def NF: Presheaf where
  Pred Γ t T := exists t', t.eq t' ∧ Tm.NF Γ t' T
  weaken {Γ' Γ t T} := by
    rintro ⟨t', E, N⟩
    exists t'.up 0 Γ'.length
    and_intros
    . apply E.up
    . apply N.weaken_app



instance: NF.HasNeutral where
  NE := NE
  atom {Γ t} := by
    intro H
    simp [NE, NF] at *
    rcases H with ⟨t', E, N⟩
    exists t'
    and_intros
    . exact E
    . apply Tm.NF.atom
      exact N
  var {Γ T} := by
    simp [NE]
    exists (.var 0)
    and_intros
    . apply ECl.refl
    . apply Tm.NE.var
      simp
  imp {Γ Γ' t s A B} := by
    rintro ⟨t', Et', Nt'⟩
    rintro ⟨s', Es', Ns'⟩
    exists (t'.up 0 Γ'.length).app s'
    and_intros
    . apply Tm.eq.app
      . apply Et'.up
      . exact Es'
    . apply Tm.NE.app
      . apply Nt'.weaken_app
      . exact Ns'
  app_inv {Γ t A B} := by
    rintro ⟨t', E, N⟩
    exists t'.abs
    and_intros
    . apply ECl.rstep
      . apply Tm.step.eta
      . apply Tm.eq.abs
        exact E
    . apply Tm.NF.abs
      exact N


theorem step_forces' {Γ: Context} {t t': Tm} {T}:
  t.step t' ->
  NF.forces Γ t' T ->
  NF.forces Γ t T
:= by
  intro S F
  induction T generalizing Γ t t' with
  | Atom =>
    simp [Presheaf.forces, forcePred] at *
    obtain ⟨t'', S', N⟩ := F
    exists t''
    and_intros
    . apply ECl.step
      . exact S
      . exact S'
    . exact N
  | imp T1 T2 IH1 IH2 =>
    simp [Presheaf.forces, forcePred] at *
    intro s Γ' F'
    apply IH2
    . apply Tm.step.app1
      apply Tm.step.up
      exact S
    . apply F
      exact F'


instance: NF.MSubst where
  msubst {Γ t T1 T2 Δ Δ' s env} HT I N F := by
    apply step_forces' _ F
    simp [Tm.up, Tm.msubst]
    apply Tm.step.compute
    . apply Tm.step.appAbs
    apply Tm.msubst_le_step
    generalize Δ'.length = n
    replace HT := HT.bound
    simp_all [I.length]


/--
This is the result of the real completeness
-/
theorem Tm.NF_halts {Γ: Context} {t T}:
  Γ.Typing t T -> exists t', t.eq t' ∧ Tm.NF Γ t' T
:= by
  intro HT
  let entailment := NF.soundness HT
  specialize entailment Γ (Env.vars Γ.length) Satisfy.self
  simp at entailment
  apply NF.completeness
  exact entailment
