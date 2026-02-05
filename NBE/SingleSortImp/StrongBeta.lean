import NBE.SingleSortImp.Presheaf
import NBE.SingleSortImp.Beta


namespace SingleSortImp

namespace StrongBeta


def NFPred (t: Tm): Prop :=
  Not (exists f: Nat -> Tm, f 0 = t ∧ forall n, (f n).beta_step (f (n + 1)))


theorem NFPred.weaken_succ {t: Tm} {n}:
  NFPred (t.up 0 n) -> NFPred (t.up 0 (n+1))
:= by
  intro H
  intro contra
  obtain ⟨f, E, S⟩ := contra
  apply H
  let f': Nat -> Tm := fun x => (f x).down 0
  exists f'
  and_intros
  . simp [f']
    simp [E]
  . intro n
    simp [f']
    apply (S n).down


theorem NFPred.weaken {t: Tm} {n}:
  NFPred t -> NFPred (t.up 0 n)
:= by
  intro H
  induction n
  case zero =>
    simp_all
  case succ n IH =>
    apply NFPred.weaken_succ
    exact IH


inductive NEPred: Tm -> Prop where
  | var {x: Nat}: NEPred (.var x)
  | app {t1 t2: Tm}: NEPred t1 -> NFPred t2 -> NEPred (t1.app t2)


theorem NEPred.weaken {t: Tm} {n}:
  NEPred t -> NEPred (t.up 0 n)
:= by
  intro H
  induction H
  case var =>
    simp [Tm.up]
    constructor
  case app t1 t2 N1 N2 IH =>
    simp [Tm.up]
    constructor
    . exact IH
    . apply NFPred.weaken
      exact N2


theorem NEPred.NF (t: Tm):
  NEPred t -> NFPred t
:= by
  intro h
  induction h
  case var =>
    unfold NFPred
    rintro ⟨f, E, S⟩
    specialize S 0
    simp [E] at S
    cases S
  case app t1 t2 N1 N2 IH =>
    rintro ⟨f, E, S⟩
    let S0 := S 0
    simp [E] at S0
    admit



def NF: Presheaf where
  Pred Γ t T := NFPred t
  weaken {Γ' Γ t T} := by
    intro N
    apply N.weaken


def NE: Presheaf where
  Pred Γ t T := NEPred t
  weaken {Γ' Γ t T} := by
    intro N
    apply N.weaken


def NE.NF {Γ t T}:
  NE Γ t T -> NF Γ t T
:= by
  rintro N
  apply NEPred.NF
  exact N


instance NF.hasNeutral: NF.HasNeutral where
  NE := NE
  atom {Γ t} := by
    intro N
    apply NE.NF
    exact N
  imp {Γ Γ' t s A B} := by
    intro Nt Ns
    apply NEPred.app
    . apply Nt.weaken
    . exact Ns
  var {Γ A} := by
    constructor
  app_inv {Γ t A B} := by
    intro N
    rintro ⟨f, E, S⟩
    apply N
    let f': Nat -> Tm := fun n => (f n).up0.app (.var 0)
    exists f'
    and_intros
    . simp [f', Tm.up0]
      simp [E]
    . intro n
      simp [f']
      apply Tm.beta_step.app1
      apply Tm.beta_step.up
      apply S


instance: NF.ABSInv where
  abs_inv {Γ t t' T} := by
    admit


theorem Tm.strongly_normalizing {Γ: Context} {t T}:
  Γ.Typing t T -> Not (exists f: Nat -> Tm, f 0 = t ∧ forall n, (f n).beta_step (f (n + 1)))
:= by
  intro HT
  have H := NF.normalize HT
  simp [NF] at H
  exact H
