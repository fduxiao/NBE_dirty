import NBE.SingleSortImp.BetaEta
import NBE.SingleSortImp.Presheaf

namespace SingleSortImp

def normalize_NE (T: Ty) (t: Tm): Tm :=
  match T with
  | .Atom => t
  | .imp T1 T2 =>
    .abs $ normalize_NE T2 (t.up0.app (normalize_NE T1 (.var 0)))


theorem Tm.NE.normalize_NF {Γ: Context} {t T}:
  Tm.NE Γ t T ->
  Tm.NF Γ (normalize_NE T t) T
:= by
  intro N
  induction T generalizing Γ t
  case Atom =>
    simp [normalize_NE]
    apply Tm.NF.atom
    exact N
  case imp T1 T2 IH1 IH2 =>
    simp [normalize_NE]
    apply Tm.NF.abs
    apply IH2
    apply Tm.NE.app
    . apply Tm.NE.weaken_cons
      exact N
    . apply IH1
      apply Tm.NE.var
      simp


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
    . rfl
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
    . apply Tm.step.eta.rstep
      . apply Tm.eq.abs
        exact E
    . apply Tm.NF.abs
      exact N


theorem step_forces' {Γ: Context} {t t': Tm} {T}:
  t.beta_step t' ->
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
    . replace S := S.step.eq
      apply S.trans
      exact S'
    . exact N
  | imp T1 T2 IH1 IH2 =>
    simp [Presheaf.forces, forcePred] at *
    intro s Γ' F'
    apply IH2
    . apply Tm.beta_step.app1
      apply Tm.beta_step.up
      exact S
    . apply F
      exact F'


instance: NF.BetaStep where
  beta_step {Γ: Context} {t t': Tm} {T} := by
    intro S N
    obtain ⟨t'', S', N⟩ := N
    exists t''
    and_intros
    . replace S := S.step.eq
      apply S.trans
      exact S'
    . exact N


/--
This is the result of the real completeness
-/
theorem Tm.NF_halts {Γ: Context} {t T}:
  Γ.Typing t T -> exists t', t.eq t' ∧ Tm.NF Γ t' T
:= by
  intro HT
  have H := NF.normalize HT
  simp [NF] at H
  exact H
