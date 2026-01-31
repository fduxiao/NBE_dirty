import NBE.SingleSortImp.Beta
import NBE.SingleSortImp.Presheaf


namespace SingleSortImp

namespace BetaNormalizing

def BNE: Presheaf where
  Pred Γ t T := exists t', t.beta_eq t' ∧ t'.BNE
  weaken {Γ' Γ t T} := by
    intro ⟨t', E, B⟩
    exists t'.up 0 Γ'.length
    and_intros
    . apply E.up
    . exact B.up


def BNF: Presheaf where
  Pred Γ t T := exists t', t.beta_eq t' ∧ t'.BNF
  weaken {Γ' Γ t T} := by
    intro ⟨t', E, B⟩
    exists t'.up 0 Γ'.length
    and_intros
    . apply E.up
    . exact B.up


theorem abs_up_app_beta_step {t: Tm}:
  (t.abs.up0.app (.var 0)).beta_step t
:= by
  simp [Tm.up0, Tm.up]
  apply Tm.beta_step.compute Tm.beta_step.appAbs_ssubst
  simp [Tm.up_ssubst]
  conv =>
    rhs
    rewrite [Tm.ssubst_id t]
  congr
  funext n
  cases n with
  | zero =>
    simp [Subst.comp, Subst.step, Tm.ssubst, Subst.up, Subst.id]
  | succ =>
    simp [Subst.comp, Subst.step, Tm.ssubst, Subst.up, Subst.id]


theorem beta_eq_normal_beta_mstep {t n: Tm}:
  t.beta_eq n -> n.beta_normal -> t.beta_mstep n
:= by
  intro S N
  obtain ⟨s, Hts, Hsn⟩ := Relation.church_rosser Tm.beta_step S
  have E := N.MNormal Hsn
  cases E
  exact Hts


theorem beta_mstep_app_var_normal' {t s: Tm}:
  t.beta_eq t.down0.up0 ->
  (t.app (.var 0)).beta_mstep s ->
  s.BNF ->
  exists t', t.beta_mstep t' ∧ t'.BNF
:= by
  intro I S N
  generalize E: (t.app (.var 0)) = m at S
  induction S generalizing t with
  | refl =>
    rewrite [<-E] at N
    exists t
    and_intros
    . apply RTCl.refl
    . grind [Tm.BNE, Tm.BNF]
  | step Hxy Hyz IH =>
    cases Hxy with
    | abs =>
      cases E
    | app2 =>
      cases E
      exists t
    | app1 S' =>
      cases E
      rename_i t'
      have I: t'.beta_eq t'.down0.up0 := by
        apply ECl.trans
        . apply ECl.reverse
          exact S'
        apply ECl.trans
        . apply I
        apply Tm.beta_eq.up
        apply Tm.beta_eq.down
        apply ECl.inclusion
        exact S'
      obtain ⟨t'', S'', N⟩ := IH I N (by eq_refl)
      exists t''
      and_intros
      . apply RTCl.step
        . apply S'
        . apply S''
      . exact N
    | appAbs =>
      cases E
      rename_i s M
      have S1: (M.abs.app (.var 0)).beta_eq s := by
        apply ECl.step
        . apply Tm.beta_step.appAbs
        . apply RTCl.sub_ecl
          exact Hyz
      have S2: (M.abs.app (.var 0)).beta_eq (M.down 1) := by
        -- we first change the left to `M.abs.down0.up0`
        apply ECl.trans
        . apply Tm.beta_eq.app1
          exact I
        simp [Tm.down0, Tm.down]
        apply ECl.step
        . apply abs_up_app_beta_step
        apply ECl.refl

      have S3: M.abs.down0.beta_eq s.abs := by
        simp [Tm.down0, Tm.down]
        apply Tm.beta_eq.abs
        apply ECl.trans
        . apply ECl.symm
          exact S2
        . exact S1

      rewrite [Tm.subst_up_down_var0] at Hyz
      exists s.abs.up0
      have N: s.abs.up0.BNF := by
        apply Tm.BNF.up
        apply Tm.BNF.abs
        apply N
      and_intros
      . apply beta_eq_normal_beta_mstep _ N.beta_normal
        apply ECl.trans
        . exact I
        apply Tm.beta_eq.up
        exact S3
      . exact N


theorem beta_eq_app_var_normal {t s: Tm}:
  ((t.up0.app (.var 0)).beta_eq s) -> s.BNF -> exists t', t.beta_eq t' ∧ t'.BNF
:= by
  intro S N
  replace S := beta_eq_normal_beta_mstep S N.beta_normal
  have E: t.up0.beta_eq (t.up0.down0.up0) := by simp; apply ECl.refl
  obtain ⟨s, S, N⟩ := beta_mstep_app_var_normal' E S N
  exists s.down0
  and_intros
  . apply RTCl.sub_ecl
    apply Tm.beta_mstep.up_down
    exact S
  . apply N.down


instance: BNF.HasNeutral where
  NE := BNE
  atom {Γ t} := by
    simp [BNE, BNF]
    grind [Tm.BNE, Tm.BNF]

  imp {Γ Γ'} {t s} {A B} := by
    rintro ⟨t', Et', Nt'⟩
    rintro ⟨s', Es', Ns'⟩
    exists (t'.up 0 Γ'.length).app s'
    and_intros
    . apply Tm.beta_eq.app
      . apply Et'.up
      . exact Es'
    . apply Tm.BNE.app
      . apply Nt'.up
      . apply Ns'
  var {Γ A} := by
    simp [BNE]
    exists (.var 0)
    and_intros
    . apply ECl.refl
    . constructor
  app_inv {Γ t A B} := by
    rintro ⟨s, E, N⟩
    apply beta_eq_app_var_normal
    . apply E
    . exact N


theorem beta_step_forces' {Γ: Context} {t t': Tm} {T}:
  t.beta_step t' ->
  BNF.forces Γ t' T ->
  BNF.forces Γ t T
:= by
  intro S F
  induction T generalizing Γ t t' with
  | Atom =>
    simp [Presheaf.forces, forcePred] at *
    and_intros
    . obtain ⟨t'', S', N⟩ := F
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
    . apply Tm.beta_step.app1
      apply Tm.beta_step.up
      exact S
    . apply F
      exact F'


instance: BNF.BetaStep where
  beta_step {Γ: Context} {t t': Tm} {T} := by
    intro S N
    obtain ⟨t'', S', N⟩ := N
    exists t''
    and_intros
    . apply ECl.step
      . exact S
      . exact S'
    . exact N


/--
This is the result of the real completeness.
-/
theorem beta_step_normalizing {Γ: Context} {t T}:
  Γ.Typing t T -> exists t', t.beta_eq t' ∧ t'.BNF
:= by
  intro HT
  have H := BNF.normalize HT
  simp [BNF] at H
  exact H
