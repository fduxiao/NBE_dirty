import NBE.Rel
import NBE.Map
import NBE.SingleSortImp.Beta

namespace SingleSortImp

/-!
### equalities between Morphisms
-/


inductive Tm.step: Tm -> Tm -> Prop where
  -- beta reduction
  | appAbs {t s: Tm}: Tm.step (.app t.abs s) (t.subst 0 s.up0).down0
  -- eta reduction
  | eta {t: Tm}: Tm.step (t.up0.app $ .var 0).abs t
  -- congrunence relation
  | abs {t1 t2: Tm}: Tm.step t1 t2 -> Tm.step t1.abs t2.abs
  | app1 {t1 t2 s: Tm}: Tm.step t1 t2 -> Tm.step (.app t1 s) (.app t2 s)
  | app2 {t s1 s2: Tm}: Tm.step s1 s2 -> Tm.step (.app t s1) (.app t s2)


theorem Tm.beta_step.step {t1 t2: Tm}:
  t1.beta_step t2 -> t1.step t2
:= by
  intro H
  induction H
  case appAbs =>
    apply Tm.step.appAbs
  case app1 | app2 | abs =>
    grind [Tm.step]


def Tm.mstep: Tm -> Tm -> Prop := RTCl Tm.step
def Tm.eq := ECl Tm.step
def Tm.normal := Relation.Normal Tm.step



theorem Tm.mstep.abs {t1 t2: Tm}:
  t1.mstep t2 -> t1.abs.mstep t2.abs
:= by
  apply RTCl.keep_cong Tm.step.abs


theorem Tm.mstep.app1 {t1 t2 s: Tm}:
  t1.mstep t2 -> (t1.app s).mstep (t2.app s)
:= by
  apply RTCl.keep_cong Tm.step.app1


theorem Tm.mstep.app2 {t s1 s2: Tm}:
  s1.mstep s2 -> (t.app s1).mstep (t.app s2)
:= by
  apply RTCl.keep_cong Tm.step.app2


theorem Tm.mstep.app {t1 t2 s1 s2: Tm}:
  t1.mstep t2 ->
  s1.mstep s2 ->
  (t1.app s1).mstep (t2.app s2)
:= by
  intro St Ss
  apply RTCl.trans
  . apply Tm.mstep.app1
    exact St
  . apply Tm.mstep.app2
    exact Ss


theorem Tm.eq.abs {t1 t2: Tm}:
  t1.eq t2 -> t1.abs.eq t2.abs
:= by
  apply ECl.keep_cong Tm.step.abs


theorem Tm.eq.app1 {t1 t2 s: Tm}:
  t1.eq t2 -> (t1.app s).eq (t2.app s)
:= by
  apply ECl.keep_cong Tm.step.app1


theorem Tm.eq.app2 {t s1 s2: Tm}:
  s1.eq s2 -> (t.app s1).eq (t.app s2)
:= by
  apply ECl.keep_cong Tm.step.app2


theorem Tm.eq.app {t1 t2 s1 s2: Tm}:
  t1.eq t2 -> s1.eq s2 -> (t1.app s1).eq (t2.app s2)
:= by
  intro H1 H2
  apply ECl.trans
  . apply H1.app1
  . apply H2.app2


theorem Tm.step.typing {Γ: Context} {t t': Tm} {T}:
  t.step t' -> Γ.Typing t T -> Γ.Typing t' T
:= by
  intro S HT
  induction HT generalizing t' with
  | var H =>
    cases S
  | abs H IH =>
    cases S with
    | abs S =>
      specialize IH S
      constructor
      exact IH
    | eta =>
      cases H with | app H1 H2 =>
      cases H2 with | var H2 =>
      simp_all
      apply Context.weaken_cons_inv
      apply H1
  | app H1 H2 IH1 IH2 =>
    cases S with
    | appAbs =>
      cases H1
      apply Context.subst_typing
      . assumption
      . exact H2
    | app1 S =>
      constructor
      . apply IH1
        exact S
      . exact H2
    | app2 S =>
      constructor
      . exact H1
      . apply IH2
        exact S


theorem Tm.mstep.typing {Γ: Context} {t t': Tm} {T}:
  t.mstep t' -> Γ.Typing t T -> Γ.Typing t' T
:= by
  intro S HT
  induction S with
  | refl =>
    apply HT
  | step Hxy Hyz IH =>
    apply IH
    apply Hxy.typing
    exact HT


mutual
  inductive Tm.NE: Context -> Tm -> Ty -> Prop where
    | var {Γ: Context} {x} {T}: Γ.lookup x = some T -> Tm.NE Γ (.var x) T
    | app {Γ} {t s} {T1 T2}: Tm.NE Γ t (T1.imp T2) -> Tm.NF Γ s T1 -> Tm.NE Γ (t.app s) T2

  inductive Tm.NF: Context -> Tm -> Ty -> Prop where
    | atom {Γ} {t}: Tm.NE Γ t .Atom -> Tm.NF Γ t .Atom
    | abs {Γ} {t} {T1 T2}: Tm.NF (T1 :: Γ) t T2 -> Tm.NF Γ t.abs (T1.imp T2)
end


theorem Tm.NE.atom {Γ t}:
  Tm.NE Γ t .Atom -> Tm.NF Γ t .Atom
:= by
  apply Tm.NF.atom


theorem Tm.NFNE.typing {Γ: Context} {t T}:
  (Tm.NF Γ t T -> Γ.Typing t T) ∧ (Tm.NE Γ t T -> Γ.Typing t T)
:= by
  induction t generalizing Γ T with
  | _ =>
    grind [Tm.NF, Tm.NE, Context.Typing]


theorem Tm.NF.typing {Γ: Context} {t T}:
  Tm.NF Γ t T -> Γ.Typing t T
:= by
  apply Tm.NFNE.typing.left

theorem Tm.NE.typing {Γ: Context} {t T}:
  Tm.NE Γ t T -> Γ.Typing t T
:= by
  apply Tm.NFNE.typing.right


theorem Tm.N_weakening {Γ2 Γ3 Γ1 T} {t: Tm}:
  (Tm.NE (Γ2 ++ Γ1) t T <-> Tm.NE (Γ2 ++ (Γ3 ++ Γ1)) (t.up Γ2.length Γ3.length) T) ∧
  (Tm.NF (Γ2 ++ Γ1) t T <-> Tm.NF (Γ2 ++ (Γ3 ++ Γ1)) (t.up Γ2.length Γ3.length) T)
:= by
  induction t generalizing Γ1 Γ2 Γ3 T with
  | var x =>
    and_intros
    . apply Iff.intro
      . intro N
        cases N with | var H =>
        constructor
        split
        . grind [FinMap.lookup]
        . have I: x ≥ Γ2.length := by omega
          simp [FinMap.lookup_right I] at H
          have I: x + Γ3.length ≥ Γ2.length := by omega
          simp [FinMap.lookup_right I]
          grind [FinMap.lookup]
      . intro N
        cases N with | var H =>
        constructor
        split at H
        . grind [FinMap.lookup]
        . have I: x ≥ Γ2.length := by omega
          simp [FinMap.lookup_right I]
          have I: x + Γ3.length ≥ Γ2.length := by omega
          simp [FinMap.lookup_right I] at H
          grind [FinMap.lookup]
    . apply Iff.intro
      . intro N
        cases N with | atom N =>
        cases N with | var H =>
        constructor
        constructor
        split
        . grind [FinMap.lookup]
        . next I =>
          have I: x ≥ Γ2.length := by omega
          simp [FinMap.lookup_right I] at H
          have I: x + Γ3.length ≥ Γ2.length := by omega
          simp [FinMap.lookup_right I]
          grind [FinMap.lookup]
      . intro N
        cases N with | atom N =>
        cases N with | var H =>
        constructor
        constructor
        split at H
        . grind [FinMap.lookup]
        . have I: x ≥ Γ2.length := by omega
          simp [FinMap.lookup_right I]
          have I: x + Γ3.length ≥ Γ2.length := by omega
          simp [FinMap.lookup_right I] at H
          grind [FinMap.lookup]
  | app t1 t2 IH1 IH2 =>
    and_intros
    . apply Iff.intro
      . intro N
        cases N with | app N1 N2 =>
        constructor
        . apply IH1.left.mp
          exact N1
        . apply IH2.right.mp
          exact N2
      . intro N
        cases N with | app N1 N2 =>
        constructor
        . apply IH1.left.mpr
          exact N1
        . apply IH2.right.mpr
          exact N2
    . apply Iff.intro
      . intro N
        cases N with | atom N =>
        cases N with | app N1 N2 =>
        constructor
        constructor
        . apply IH1.left.mp
          exact N1
        . apply IH2.right.mp
          exact N2
      . intro N
        cases N with | atom N =>
        cases N with | app N1 N2 =>
        constructor
        constructor
        . apply IH1.left.mpr
          exact N1
        . apply IH2.right.mpr
          exact N2
  | abs M IH =>
    and_intros
    . apply Iff.intro
      . intro N
        cases N
      . intro N
        cases N
    . apply Iff.intro
      . intro N
        cases N with
        | atom N => cases N
        | abs N =>
          constructor
          grind [Tm.NE, Tm.NF]
      . intro N
        cases N with
        | atom N => cases N
        | abs N =>
          constructor
          grind [Tm.NE, Tm.NF]


theorem Tm.NE.weaken_app {Γ' Γ T} {t: Tm}:
  Tm.NE Γ t T -> Tm.NE (Γ' ++ Γ) (t.up 0 Γ'.length) T
:= by
  let H := (Tm.N_weakening (Γ2 := []) (Γ3 := Γ') (Γ1 := Γ) (t := t) (T := T))
  simp at H
  apply H.left.mp


theorem Tm.NE.weaken_cons {A Γ T} {t: Tm}:
  Tm.NE Γ t T -> Tm.NE (A :: Γ) t.up0 T
:= by
  let H := (Tm.N_weakening (Γ2 := []) (Γ3 := [A]) (Γ1 := Γ) (t := t) (T := T))
  simp at H
  apply H.left.mp


theorem Tm.NF.weaken_app {Γ' Γ T} {t: Tm}:
  Tm.NF Γ t T -> Tm.NF (Γ' ++ Γ) (t.up 0 Γ'.length) T
:= by
  let H := (Tm.N_weakening (Γ2 := []) (Γ3 := Γ') (Γ1 := Γ) (t := t) (T := T))
  simp at H
  apply H.right.mp


/-!
We know some facts about reduction. We first need the following lemma to perform a
`step` operation.
-/

/--
This is trivial, but there could be some situation that the `t` is not `step` to a
substitution. Then, you can apply this theorem to intro the `t'` in order to do the computation.
-/
theorem Tm.step.compute {t t' t'': Tm}:
  t.step t' -> t' = t'' -> t.step t''
:= by
  intro H E
  simp_all


theorem Tm.step.appAbs_ssubst {t s: Tm}:
  (t.abs.app s).step (t.ssubst (.step s))
:= by
  apply Tm.step.compute
  . apply Tm.step.appAbs
  . apply Tm.step_ssubst


@[simp]
theorem Tm.up0_ssubst_abs {t: Tm} {s: Subst}:
  (t.up0.ssubst s.abs) = (t.ssubst s).up0
:= by
  unfold up0
  simp [Tm.up_ssubst]
  apply Tm.ssubst_congr
  intro n
  simp [Subst.comp]
  cases n with
  | _ =>
    simp [Tm.ssubst, Subst.up, Subst.abs]
    unfold up0
    simp [Tm.up_ssubst]


theorem Tm.step.ssubst {t1 t2: Tm} {s: Subst}:
  t1.step t2 ->
  (t1.ssubst s).step (t2.ssubst s)
:= by
  intro S
  induction S generalizing s with
  | appAbs =>
    rename_i t11 t12
    rewrite [Tm.step_ssubst]
    simp [Tm.ssubst]
    apply Tm.step.compute
    . apply Tm.step.appAbs_ssubst
    simp
    apply Tm.ssubst_congr
    intro n
    simp [Subst.comp]
    cases n with
    | zero =>
      simp [Subst.step, Subst.abs, Tm.ssubst]
    | succ m =>
      simp [Subst.step, Subst.abs, Tm.ssubst]
  | eta =>
    simp [Tm.ssubst, Subst.abs]
    rename_i t
    apply eta
  | abs S IH =>
    constructor
    apply IH
  | app1 S IH =>
    apply Tm.step.app1
    apply IH
  | app2 S IH =>
    apply Tm.step.app2
    apply IH



/--
The shift is congruent over `step`
-/
theorem Tm.step.up {c n} {t t': Tm}:
  t.step t' -> (t.up c n).step (t'.up c n)
:= by
  simp [Tm.up_ssubst]
  apply Tm.step.ssubst


theorem Tm.mstep.up {c n} {t t': Tm}:
  t.eq t' -> (t.up c n).eq (t'.up c n)
:= by
  intro S
  apply ECl.keep_cong Tm.step.up
  exact S


theorem Tm.eq.up {c n} {t t': Tm}:
  t.eq t' -> (t.up c n).eq (t'.up c n)
:= by
  intro S
  apply ECl.keep_cong Tm.step.up
  exact S


theorem Tm.step.down {c} {t t': Tm}:
  t.step t' -> (t.down c).step (t'.down c)
:= by
  simp [Tm.down_ssubst]
  apply Tm.step.ssubst


theorem Tm.mstep.down {c} {t t': Tm}:
  t.mstep t' -> (t.down c).mstep (t'.down c)
:= by
  apply RTCl.keep_cong Tm.step.down


theorem Tm.eq.down {c} {t t': Tm}:
  t.eq t' -> (t.down c).eq (t'.down c)
:= by
  apply ECl.keep_cong Tm.step.down


theorem Tm.mstep.up_down {t t': Tm}:
  t.up0.mstep t' -> t.mstep t'.down0
:= by
  intro H
  replace H := Tm.mstep.down H (c := 0)
  simp [Tm.up0] at H
  exact H


theorem Tm.BNE.BNF {t: Tm}:
  t.BNE -> t.BNF
:= by
  intro H
  constructor
  exact H


theorem Tm.BN.up {t: Tm} {c n}:
  (t.BNE <-> (t.up c n).BNE) ∧ (t.BNF <-> (t.up c n).BNF)
:= by
  induction t generalizing c n <;>
  grind [up, BNE, BNF]


theorem Tm.step.BN {t s: Tm}:
  t.step s ->
  (t.BNE -> s.BNE) ∧ (t.BNF -> s.BNF)
:= by
  intro S
  induction S with try grind [BNE, BNF]
  | eta =>
    rename_i t
    and_intros
    . intro N
      cases N
    . intro N
      cases N <;> try contradiction
      rename_i N
      cases N <;> try contradiction
      rename_i N
      cases N with | app N _ =>
      apply BNF.neutral
      apply BN.up.left.mpr
      exact N


theorem Tm.step.BNE {t s: Tm}:
  t.step s ->
  (t.BNE -> s.BNE)
:= by
  intro S
  apply S.BN.left


theorem Tm.step.BNF {t s: Tm}:
  t.step s ->
  (t.BNF -> s.BNF)
:= by
  intro S
  apply S.BN.right


theorem Tm.mstep.BNE {t s: Tm}:
  t.mstep s ->
  t.BNE ->
  s.BNE
:= by
  intro S N
  induction S with
  | refl =>
    exact N
  | step Hty Hys IH =>
    apply IH
    apply Hty.BN.left
    exact N


def Tm.freeVar (x: Nat): Tm -> Bool
  | .var y => y = x
  | .app t1 t2 => t1.freeVar x || t2.freeVar x
  | .abs t => t.freeVar (x + 1)


theorem Tm.not_free_up {t: Tm} {c n: Nat}:
  (forall i: Nat, c ≤ i -> i < c + n -> t.freeVar i = false) ->
  exists s: Tm, t = s.up c n
:= by
  intro H
  induction t generalizing c n with
  | var x =>
    simp [freeVar] at H
    obtain E1 | E2 : x < c ∨ x ≥ c := by omega
    . exists (.var x)
      simp [up]
      grind
    . exists .var (x - n)
      simp [up]
      grind
  | app t1 t2 IH1 IH2 =>
    simp [freeVar] at H
    obtain ⟨s1, E1⟩ := IH1 (fun i h1 h2 => (H i h1 h2).left)
    obtain ⟨s2, E2⟩ := IH2 (fun i h1 h2 => (H i h1 h2).right)
    exists s1.app s2
    simp_all [up]
  | abs t IH =>
    simp [freeVar] at H
    replace H: forall i: Nat, c + 1 ≤ i -> i < (c + 1) + n -> t.freeVar i = false := by
      intro i H1 H2
      have E: i = (i - 1) + 1 := by omega
      rewrite [E]
      grind
    obtain ⟨s, E⟩ := IH H
    exists s.abs
    simp_all [up]


theorem Tm.not_free_up0 {t: Tm}:
  t.freeVar 0 = false ->
  exists s: Tm, t = s.up0
:= by
  intro H
  apply Tm.not_free_up
  simp_all


theorem Tm.free_not_up {c n} {t s: Tm}:
  (exists i: Nat, c ≤ i ∧ i < c + n ∧ t.freeVar i = true) ->
  ¬ t = s.up c n
:= by
  intro H contra
  induction t generalizing c n s with
  | var x =>
    simp [freeVar] at H
    cases s <;> try cases contra
    grind
  | app t1 t2 IH1 IH2 =>
    simp [freeVar] at H
    obtain ⟨i, H1, H2, H⟩ := H
    cases s
    case var | abs => cases contra
    simp [up] at contra
    rename_i s1 s2
    grind
  | abs t IH =>
    simp [freeVar] at H
    obtain ⟨i, H1, H2, H⟩ := H
    cases s
    case var | app => cases contra
    rename_i s
    simp [up] at contra
    let i' := i + 1
    replace H1: c + 1 ≤ i' := by omega
    replace H2: i' < (c + 1) + n := by omega
    apply IH
    . exists i'
    . exact contra


theorem Tm.free_not_up0 {t s: Tm}:
  t.freeVar 0 = true ->
  ¬ t = s.up0
:= by
  intro H
  apply Tm.free_not_up
  simp_all


@[simp]
theorem Tm.up0_not_free {t: Tm}:
  t.up0.freeVar 0 = false
:= by
  cases E: t.up0.freeVar 0 with
  | false =>
    eq_refl
  | true =>
    exfalso
    apply Tm.free_not_up0
    . exact E
    . eq_refl


def Tm.doEta: Tm -> Tm
  | .var x => .var x
  | .app t1 t2 => t1.doEta.app t2.doEta
  | .abs t =>
    match t.doEta with
    | .app t1 (.var 0) =>
      if t1.freeVar 0 then
        .abs (t1.app (.var 0))
      else
        t1.down0
    | x => .abs x


theorem Tm.mstep_doEta {t: Tm}:
  t.mstep t.doEta
:= by
  induction t with
  | var x =>
    simp [doEta]
    apply RTCl.refl
  | app t1 t2 IH1 IH2 =>
    simp [doEta]
    apply mstep.app
    . exact IH1
    . exact IH2
  | abs t IH =>
    generalize E: t.doEta = n
    match E: n with
    | .var _ | .abs _
    | .app _ (.abs _)
    | .app _ (.app _ _)
    | .app _ (.var (_ + 1)) =>
      simp_all [doEta]
      apply IH.abs
    | .app t1 (.var 0) =>
      simp_all [doEta]
      cases E: freeVar 0 t1 with
      | true =>
        simp_all
        apply IH.abs
      | false =>
        simp
        obtain ⟨s, E⟩ := Tm.not_free_up0 E
        simp_all
        apply RTCl.trans
        . apply IH.abs
        apply RTCl.inclusion
        apply step.eta


theorem Tm.BNF.doEta {t: Tm}:
  t.BNF -> t.doEta.normal
:= by
  intro N
  induction t with
  | var x =>
    simp [Tm.doEta] at *
    intro ⟨_, contra⟩
    contradiction
  | app t1 t2 IH1 IH2 =>
    simp [Tm.doEta]
    cases N with | neutral N =>
    cases N with | app N1 N2 =>
    specialize IH1 (.neutral N1)
    specialize IH2 N2
    intro ⟨n, S⟩
    have N := Tm.mstep.BNE (Tm.mstep_doEta) N1
    clear N1 N2
    generalize t1.doEta = t1 at *
    generalize t2.doEta = t2 at *
    cases S with
    | app1 =>
      apply IH1
      grind
    | app2 =>
      apply IH2
      grind
    | appAbs =>
      cases N
  | abs t IH =>
    cases N <;> try contradiction
    rename_i N
    specialize IH N
    generalize E: t.doEta = n
    match E: n with
    | .var _ =>
      simp_all [Tm.doEta]
      intro ⟨_, S⟩
      contradiction
    | .abs _
    | .app _ (.abs _)
    | .app _ (.app _ _)
    | .app _ (.var (_ + 1)) =>
      simp_all [Tm.doEta]
      intro ⟨_, S⟩
      cases S with | abs S =>
      apply IH
      grind
    | .app t1 (.var 0) =>
      simp_all [Tm.doEta]
      cases E: freeVar 0 t1 with
      | true =>
        simp
        intro ⟨w, S⟩
        cases S with
        | abs S =>
          apply IH
          grind
        | eta =>
          simp_all
      | false =>
        simp
        obtain ⟨s, E⟩ := Tm.not_free_up0 E
        simp_all
        intro ⟨_, S⟩
        apply IH
        constructor
        apply step.app1
        apply S.up


theorem Tm.BNF.halts {t: Tm}:
  t.BNF -> exists n: Tm, t.mstep n ∧ n.normal
:= by
  intro N
  exists t.doEta
  and_intros
  . apply Tm.mstep_doEta
  . apply N.doEta


theorem Tm.N_to_BN {Γ} {t: Tm} {T}:
  (Tm.NE Γ t T -> t.BNE) ∧ (Tm.NF Γ t T -> t.BNF)
:= by
  induction t generalizing Γ T with
  | _ =>
    grind [Tm.NE, Tm.NF, BNE, BNF]


theorem Tm.NE.BNE {Γ t T}:
  Tm.NE Γ t T -> t.BNE
:= by
  apply Tm.N_to_BN.left


theorem Tm.NF.BNF {Γ t T}:
  Tm.NF Γ t T -> t.BNF
:= by
  apply Tm.N_to_BN.right


theorem Tm.normalizing {Γ} {t: Tm} {T}:
  Tm.NF Γ t T -> exists n: Tm, t.mstep n ∧ n.normal
:= by
  intro N
  apply Tm.BNF.halts
  apply N.BNF



/--
The parallel reduction relation.
-/
inductive Tm.step2: Tm -> Tm -> Prop where
  -- beta reduction
  | appAbs {t1 t2 s1 s2: Tm}: t1.step2 t2 -> s1.step2 s2 -> Tm.step2 (.app t1.abs s1) (t2.subst 0 s2.up0).down0
  -- eta
  | eta {t1 t2: Tm}: t1.step2 t2 -> (t1.up0.app (.var 0)).abs.step2 t2
  -- congrunence relation
  | abs {t1 t2: Tm}: Tm.step2 t1 t2 -> Tm.step2 t1.abs t2.abs
  | app {t1 t2 s1 s2: Tm}: Tm.step2 t1 t2 -> Tm.step2 s1 s2 -> Tm.step2 (.app t1 s1) (.app t2 s2)
  -- refl
  | var {x: Nat}: Tm.step2 (.var x) (.var x)


theorem Tm.step2.refl {t: Tm}:
  t.step2 t
:= by
  induction t <;> grind [Tm.step2]


theorem Tm.step2.app1 {t1 t2 s: Tm}:
  t1.step2 t2 ->
  (t1.app s).step2 (t2.app s)
:= by
  intro S
  apply app
  . exact S
  . apply refl


theorem Tm.step2.app2 {t s1 s2: Tm}:
  s1.step2 s2 ->
  (t.app s1).step2 (t.app s2)
:= by
  intro S
  apply app
  . apply refl
  . exact S


theorem Tm.step.step2 {t1 t2: Tm}:
  t1.step t2 -> t1.step2 t2
:= by
  intro S
  induction S with
  | appAbs =>
    apply step2.appAbs .refl .refl
  | abs S IH =>
    apply step2.abs
    apply IH
  | app1 S IH =>
    apply step2.app1
    exact IH
  | app2 S IH =>
    apply step2.app2
    exact IH
  | eta =>
    apply step2.eta
    apply step2.refl


theorem Tm.step2.mstep {t1 t2: Tm}:
  t1.step2 t2 -> t1.mstep t2
:= by
  intro S
  induction S with
  | var =>
    apply RTCl.refl
  | appAbs S1 S2 IH1 IH2 =>
    apply RTCl.trans
    . apply Tm.mstep.app1
      apply Tm.mstep.abs
      apply IH1
    apply RTCl.trans
    . apply Tm.mstep.app2
      apply IH2
    apply RTCl.inclusion
    apply step.appAbs
  | eta S IH =>
    apply RTCl.step
    . apply step.eta
    . exact IH
  | abs S IH =>
    apply mstep.abs
    exact IH
  | app S1 S2 IH1 IH2 =>
    apply mstep.app
    . apply IH1
    . apply IH2


theorem Tm.step2.compute {t t' t'': Tm}:
  t.step2 t' -> t' = t'' -> t.step2 t''
:= by
  intro H E
  simp_all


theorem Tm.step2.ssubst {t1 t2: Tm} {s: Subst}:
  t1.step2 t2 ->
  (t1.ssubst s).step2 (t2.ssubst s)
:= by
  intro S
  induction S generalizing s with
  | var =>
    apply step2.refl
  | abs S IH =>
    simp [Tm.ssubst]
    apply step2.abs
    apply IH
  | app S1 S2 IH1 IH2 =>
    simp [Tm.ssubst]
    apply step2.app
    . apply IH1
    . apply IH2
  | appAbs S1 S2 IH1 IH2 =>
    simp [Tm.ssubst]
    apply Tm.step2.compute
    . apply appAbs
      . apply IH1
      . apply IH2
    simp [Tm.step_ssubst]
    apply Tm.ssubst_congr
    intro n
    simp [Subst.comp]
    cases n with
    | zero =>
      simp [Subst.abs, Tm.ssubst, Subst.step]
    | succ =>
      simp [Subst.abs, Tm.ssubst, Subst.step]
  | eta S IH =>
    simp [Tm.ssubst]
    apply Tm.step2.compute
    . apply eta
      apply IH
    eq_refl


theorem Tm.step2.subst1 {t1 t2 s: Tm} {i}:
  t1.step2 t2 ->
  (t1.subst i s).step2 (t2.subst i s)
:= by
  simp [Tm.subst_ssubst]
  apply Tm.step2.ssubst


theorem Tm.step2.up {t1 t2: Tm} {c n}:
  t1.step2 t2 -> (t1.up c n).step2 (t2.up c n)
:= by
  simp [Tm.up_ssubst]
  apply Tm.step2.ssubst


theorem Tm.step2.down {t1 t2: Tm} {c}:
  t1.step2 t2 -> (t1.down c).step2 (t2.down c )
:= by
  simp [Tm.down_ssubst]
  apply Tm.step2.ssubst


theorem Tm.step2.subst2 {t s1 s2: Tm} {i}:
  s1.step2 s2 ->
  (t.subst i s1).step2 (t.subst i s2)
:= by
  intro S
  induction t generalizing i s1 s2 with
  | var x =>
    simp [Tm.subst]
    split
    . exact S
    . apply step2.refl
  | abs t IH =>
    simp [Tm.subst]
    apply step2.abs
    apply IH
    apply S.up
  | app t1 t2 IH1 IH2 =>
    simp [Tm.subst]
    apply Tm.step2.app
    . apply IH1
      exact S
    . apply IH2
      exact S


theorem Tm.not_free_subst_eq {t s: Tm} {i: Nat}:
  t.freeVar i = false ->
  t.subst i s = t
:= by
  induction t generalizing i s with
  | var x =>
    simp [freeVar, subst]
    grind
  | app t1 t2 IH1 IH2 =>
    simp [freeVar, subst]
    grind
  | abs t IH =>
    simp [freeVar, subst]
    grind


@[simp]
theorem Tm.up0_subst_eq {t s: Tm}:
  t.up0.subst 0 s = t.up0
:= by
  apply Tm.not_free_subst_eq
  simp


theorem Tm.subst_up0 {t s: Tm} {i}:
  (t.up0.subst (i + 1) s.up0) = (t.subst i s).up0
:= by
  unfold up0
  simp [Tm.up_ssubst, Tm.subst_ssubst]
  apply Tm.ssubst_congr
  intro n
  simp [Subst.comp, Subst.term, Subst.up, ssubst]
  split
  . eq_refl
  . simp [Subst.up, ssubst]


theorem Tm.step2.subst {t1 t2 s1 s2: Tm} {i}:
  t1.step2 t2 ->
  s1.step2 s2 ->
  (t1.subst i s1).step2 (t2.subst i s2)
:= by
  intro S1 S2
  induction S1 generalizing i s1 s2 with
  | var =>
    apply step2.subst2
    exact S2
  | abs S IH =>
    simp [Tm.subst]
    apply step2.abs
    apply IH
    apply S2.up
  | app _ _ IH1 IH2 =>
    simp [Tm.subst]
    apply step2.app
    . apply IH1
      exact S2
    . apply IH2
      exact S2
  | appAbs _ _ IH1 IH2 =>
    simp [Tm.subst]
    apply step2.compute
    . apply step2.appAbs
      . apply IH1
        exact S2.up
      . apply IH2
        exact S2
    simp [Tm.step_ssubst]
    simp [Tm.subst_ssubst, Tm.up_ssubst]
    apply Tm.ssubst_congr
    intro n
    simp [Subst.comp]
    induction n with
    | zero =>
      simp [Tm.ssubst, Subst.term, Subst.step]
    | succ n =>
      simp [Tm.ssubst, Subst.term, Subst.step]
      split
      . simp
        rewrite [Tm.ssubst_id s2]
        simp
        apply Tm.ssubst_congr
        intro n
        simp [Subst.comp]
        simp [Subst.id, Tm.ssubst, Subst.step, Subst.comp, Subst.up]
      . simp [Tm.ssubst, Subst.step]
  | eta S IH =>
    rename_i t1 t2
    simp [Tm.subst]
    simp [Tm.subst_up0]
    apply step2.eta
    apply IH
    exact S2


def Tm.eval (t: Tm): Tm :=
  match t with
  | .var x => .var x
  | .app (.abs t1) t2 => (t1.eval.subst 0 t2.eval.up0).down0
  | .app t1 t2 => .app t1.eval t2.eval
  | .abs (.app t1 (.var 0)) =>
    if t1.freeVar 0 then .abs (t1.app (.var 0)).eval else t1.down0.eval
  | .abs t => .abs t.eval
termination_by t.size
decreasing_by
  all_goals trivial


@[simp]
theorem Tm.eval_up_eta {t: Tm}:
  (t.up0.app (Tm.var 0)).abs.eval = t.eval
:= by
  simp [eval]


theorem Tm.step2_eval {t: Tm}:
  t.step2 t.eval
:= by
  induction t using strong_ind with
  | var x =>
    simp [eval]
    apply step2.refl
  | abs t IH =>
    unfold eval
    split <;> try contradiction
    next E =>  -- eta reduction
      cases t <;> try cases E
      rename_i t
      split
      . apply step2.abs
        apply IH
        trivial
      . simp_all
        obtain ⟨s, E⟩ := Tm.not_free_up0 (by assumption)
        simp_all
        apply step2.eta
        apply IH
        trivial
    next E => -- otherwise
      specialize IH t (by trivial)
      simp_all
      apply IH.abs
  | app t1 t2 IH =>
    have IH1 := IH t1 (by trivial)
    have IH2 := IH t2 (by trivial)
    cases t1 with
    | var x =>
      simp [eval]
      apply step2.app2
      exact IH2
    | app s1 s2 =>
      simp [eval]
      apply step2.app
      . apply IH1
      . apply IH2
    | abs t1 =>
      simp [eval]
      apply step2.appAbs
      . apply IH
        trivial
      . apply IH
        trivial



theorem Tm.not_free_up_not_free {t: Tm} {c n: Nat} {x}:
  t.freeVar x = false <-> (t.up c n).freeVar (Rename.up c n x) = false
:= by
  induction t generalizing c n x with
  | var =>
    grind [freeVar, Rename.up, Tm.up]
  | app =>
    grind [freeVar, Rename.up, Tm.up]
  | abs t IH =>
    simp [freeVar, Rename.up, Tm.up] at *
    have E: (x < c) = (x + 1 < c + 1) := by grind
    specialize IH (c := c + 1) (x := x + 1) (n := n)
    grind


theorem Tm.step_not_free {t s: Tm} {x c: Nat}:
  t.freeVar (Rename.up c 1 x) = false ->
  s.freeVar x = false ->
  ((t.subst c (s.up c 1)).down c).freeVar x = false
:= by
  intro H1 H2
  induction t generalizing c s x with
  | var y =>
    simp [subst, freeVar, Rename.up] at *
    split
    . simp
      exact H2
    . simp [freeVar, down]
      grind
  | app t1 t2 IH1 IH2 =>
    simp [freeVar, subst, down] at *
    grind
  | abs t IH =>
    simp [freeVar, subst, down] at *
    rewrite [Tm.up0_switch]
    apply IH
    . simp [Rename.up] at *
      grind
    . replace H2 := (not_free_up_not_free (c := 0) (n := 1)).mp H2
      simp [Rename.up] at H2
      apply H2


theorem Tm.step2.not_free {t s: Tm} {x: Nat}:
  t.step2 s ->
  t.freeVar x = false ->
  s.freeVar x = false
:= by
  intro S H
  induction S generalizing x with
  | var =>
    simp [freeVar] at *
    trivial
  | app S1 S2 IH1 IH2 =>
    simp [freeVar] at *
    grind
  | abs S IH =>
    rename_i t s
    simp [freeVar] at *
    apply IH
    exact H
  | appAbs S1 S2 IH1 IH2 =>
    rename_i t1 s1 t2 s2
    simp [freeVar] at H
    obtain ⟨H1, H2⟩ := H
    specialize IH1 H1
    specialize IH2 H2
    apply Tm.step_not_free
    simp [Rename.up]
    . exact IH1
    . exact IH2
  | eta S IH =>
    rename_i t s
    simp [freeVar] at H
    apply IH
    apply (Tm.not_free_up_not_free (c := 0) (n := 1)).mpr
    simp [Rename.up]
    apply H


theorem Tm.step2.switch {t s: Tm}:
  t.step2 s ->
  s.step2 t.eval
:= by
  intro S
  induction t using Tm.strong_ind generalizing s with
  | var x =>
    cases S
    simp [eval]
    apply step2.var
  | app t1 t2 IH =>
    cases S with
    | app S1 S2 =>
      rename_i s1 s2
      have IH1 := IH t1 (by trivial) S1
      have IH2 := IH t2 (by trivial) S2
      unfold eval
      split <;> try contradiction
      next E => -- β-redex
        simp_all; clear E
        rename_i t1 t2
        cases S1 with
        | abs S1 =>
          rename_i s1
          replace IH1 := IH t1 (by trivial) S1
          apply step2.appAbs
          . exact IH1
          . exact IH2
        | eta S1 =>
          rename_i t1
          simp at IH1
          have E: (s1.up0.app s2.up0) = (s1.up0.app (.var 0)).subst 0 s2.up0 := by
            simp [Tm.subst]
          replace E := congrArg Tm.down0 E
          simp at E
          rewrite [E]
          apply step2.down
          apply Tm.step2.subst
          . apply IH
            . trivial
            . apply step2.app1
              apply S1.up
          . apply IH2.up
      next => -- otherwise
        simp_all
        apply step2.app
        . exact IH1
        . exact IH2
    | appAbs S1 S2 =>
      rename_i t1 s1 s2
      -- we need it for
      have IH1 := IH t1 (by trivial) S1
      have IH2 := IH t2 (by trivial) S2
      simp [eval]
      apply step2.down
      apply step2.subst
      . apply IH1
      . apply IH2.up
  | abs t IH =>
    cases S with
    | eta S =>
      rename_i t
      simp
      apply IH
      . trivial
      . exact S
    | abs S =>
      rename_i s
      unfold eval
      split <;> try contradiction
      next E => -- app
        simp_all; clear E
        rename_i t
        split
        . -- not a η-redex
          apply step2.abs
          apply IH (t.app (.var 0))
          . trivial
          . exact S
        . rename_i N
          simp_all
          cases S with
          | app S1 S2 =>
            rename_i s _
            cases S2
            replace N := S1.not_free N
            obtain ⟨s, E⟩ := Tm.not_free_up0 N
            simp_all; clear E
            apply step2.eta
            apply IH
            . trivial
            . replace S1 := S1.down (c := 0)
              simp [up0] at S1
              exact S1
          | appAbs S1 S2 =>
            rename_i t s _
            cases S2
            apply IH _ (by trivial)
            simp [down0, Tm.down]
            apply step2.abs
            simp [freeVar] at N
            have E: t.down 1 = t.down 0 := by
              clear S1 IH
              rewrite [<-Nat.add_zero 1] at *
              generalize 0 = c at *
              induction t generalizing c <;>
              . grind [Tm.down, freeVar]
            rewrite [E]
            apply S1.down
      next E => -- not a η-redex
        simp_all; clear E
        apply step2.abs
        apply IH
        . trivial
        . exact S


theorem Tm.step2.eval {t1 t2: Tm}:
  t1.step2 t2 ->
  t1.eval.step2 t2.eval
:= by
  intro S
  replace S := S.switch
  apply S.switch


theorem Tm.mstep.eval {t1 t2: Tm}:
  t1.mstep t2 -> t1.eval.mstep t2.eval
:= by
  intro S
  induction S with
  | refl =>
    apply RTCl.refl
  | step Hxy Hyz IH =>
    replace Hxy := Hxy.step2
    replace Hxy := Hxy.eval
    replace Hxy := Hxy.mstep
    apply RTCl.trans
    . apply Hxy
    . apply IH


instance Tm.step.semi_confl: SemiConfluent Tm.step where
  semi_confl := by
    intro m1 m2 m3 S MS
    exists m3.eval
    and_intros
    . replace S := S.step2
      replace S := S.switch
      replace S := S.mstep
      apply RTCl.trans
      . apply S
      . apply mstep.eval
        exact MS
    . apply step2.mstep
      apply step2_eval


theorem Tm.eq.normal_same {t1 t2: Tm}:
  t1.eq t2 -> t1.normal -> t2.normal -> t1 = t2
:= by
  intro E N1 N2
  obtain ⟨s, H1s, H2s⟩ := ChurchRosser.church_rosser E
  replace N1 := N1.MNormal H1s
  replace N2 := N2.MNormal H2s
  simp_all


theorem Tm.eq.doEta {t1 t2: Tm}:
  t1.eq t2 -> t1.doEta.eq t2.doEta
:= by
  intro E
  apply ECl.trans
  . apply ECl.symm
    apply RTCl.sub_ecl
    apply Tm.mstep_doEta
  apply ECl.trans
  . exact E
  apply RTCl.sub_ecl
  . apply Tm.mstep_doEta


theorem Tm.eq.doEta_inv {t1 t2: Tm}:
  t1.doEta.eq t2.doEta -> t1.eq t2
:= by
  intro E
  apply ECl.trans
  . apply RTCl.sub_ecl
    apply Tm.mstep_doEta
  apply ECl.trans
  . exact E
  apply ECl.symm
  . apply RTCl.sub_ecl
    apply Tm.mstep_doEta


theorem Tm.eq.doEta_same {t1 t2: Tm}:
  t1.eq t2 ->
  t1.BNF -> t2.BNF ->
  t1.doEta = t2.doEta
:= by
  intro E N1 N2
  replace E := E.doEta
  apply E.normal_same
  . apply N1.doEta
  . apply N2.doEta


theorem Tm.abs_up_app_step {t: Tm}:
  (t.abs.up0.app (.var 0)).step t
:= by
  simp [up0, up]
  apply Tm.step.compute Tm.step.appAbs_ssubst
  simp [Tm.up_ssubst]
  conv =>
    rhs
    rewrite [Tm.ssubst_id t]
  congr
  funext n
  cases n with
  | zero =>
    simp [Subst.comp, Subst.step, ssubst, Subst.up, Subst.id]
  | succ =>
    simp [Subst.comp, Subst.step, ssubst, Subst.up, Subst.id]


theorem Tm.eq.abs_inv {t s: Tm}:
  t.abs.eq s.abs -> t.eq s
:= by
  intro E
  apply ECl.rstep
  . apply Tm.abs_up_app_step
  apply ECl.trans
  . apply Tm.eq.app1
    apply E.up
  apply ECl.inclusion
  apply Tm.abs_up_app_step


theorem Tm.NE.type_unique {Γ: Context} {t: Tm} {T1 T2}:
  Tm.NE Γ t T1 -> Tm.NE Γ t T2 -> T1 = T2
:= by
  intro N1 N2
  induction t generalizing Γ T1 T2 with
  | var x =>
    cases N1
    cases N2
    simp_all
  | app t1 t2 IH1 IH2 =>
    cases N1 with | app N11 N12 =>
    cases N2 with | app N21 N22 =>
    specialize IH1 N11 N21
    simp_all
  | abs =>
    cases N1


theorem Tm.BNE.type_unique {Γ: Context} {t: Tm} {T1 T2}:
  t.BNE ->
  Γ.Typing t T1 -> Γ.Typing t T2 -> T1 = T2
:= by
  intro N HT1 HT2
  induction t generalizing Γ T1 T2 with
  | var x =>
    cases HT1
    cases HT2
    simp_all
  | app t1 t2 IH1 IH2 =>
    cases N with | app N _ =>
    cases HT1 with | app HT1 _ =>
    cases HT2 with | app HT2 _ =>
    specialize IH1 N HT1 HT2
    simp_all
  | abs =>
    cases N


theorem Tm.BNE.eq_type_unique {Γ: Context} {t s: Tm} {T1 T2}:
  t.eq s -> t.BNE -> s.BNE ->
  Γ.Typing t T1 -> Γ.Typing s T2 -> T1 = T2
:= by
  intro E N1 N2 HT1 HT2
  replace HT1: Γ.Typing t.doEta T1 := by
    apply Tm.mstep.typing
    apply Tm.mstep_doEta
    exact HT1
  replace HT2: Γ.Typing s.doEta T2 := by
    apply Tm.mstep.typing
    apply Tm.mstep_doEta
    exact HT2
  replace E := E.doEta_same N1.BNF N2.BNF
  rewrite [E] at HT1
  have N: s.doEta.BNE := by
    apply Tm.mstep.BNE
    apply Tm.mstep_doEta
    exact N2
  apply N.type_unique
  . exact HT1
  . exact HT2


theorem Tm.N_uniqueness {Γ} {t s: Tm} {T}:
  t.eq s ->
  (Tm.NF Γ t T -> Tm.NF Γ s T -> t = s) ∧ (Tm.NE Γ t T -> Tm.NE Γ s T -> t = s)
:= by
  intro E
  induction t generalizing s Γ T with
  | var x =>
    have H: (Tm.NE Γ (var x) T -> Tm.NE Γ s T -> (var x) = s) := by
      intro N1 N2
      cases s with
      | abs =>
        cases N2
      | app s1 s2 =>
        replace E := E.doEta_same N1.BNE.BNF N2.BNE.BNF
        simp [doEta] at E
      | var y =>
        replace E := E.doEta_same N1.BNE.BNF N2.BNE.BNF
        simp_all [doEta]
    and_intros
    . intro N1 N2
      cases N1 with | atom N1 =>
      cases N2 with | atom N2 =>
      solve_by_elim
    . apply H
  | app t1 t2 IH1 IH2 =>
    have H: (Tm.NE Γ (t1.app t2) T -> Tm.NE Γ s T -> (t1.app t2) = s) := by
      intro N1 N2
      cases s with
      | abs =>
        cases N2
      | var x =>
        replace E := E.doEta_same N1.BNE.BNF N2.BNE.BNF
        simp [doEta] at E
      | app s1 s2 =>
        replace E := E.doEta_same N1.BNE.BNF N2.BNE.BNF
        simp [doEta] at E
        obtain ⟨E1, E2⟩ := E
        replace E1: t1.eq s1 := by
          apply Tm.eq.doEta_inv
          rewrite [E1]
          apply ECl.refl
        replace E2: t2.eq s2 := by
          apply Tm.eq.doEta_inv
          rewrite [E2]
          apply ECl.refl
        -- Normality
        cases N1 with | app N11 N12 =>
        cases N2 with | app N21 N22 =>
        -- which forces the type
        have E := Tm.BNE.eq_type_unique E1 N11.BNE N21.BNE N11.typing N21.typing
        cases E
        replace IH1 := (IH1 E1).right N11 N21
        replace IH2 := (IH2 E2).left N12 N22
        simp_all
    and_intros
    . intro N1 N2
      cases N1 with | atom N1 =>
      cases N2 with | atom N2 =>
      solve_by_elim
    . apply H
  | abs t IH =>
    and_intros
    . intro N1 N2
      cases N1 <;> try contradiction
      rename_i T1 T2 N1
      cases N2 with | abs N2 =>
      rename_i s
      replace E := E.abs_inv
      replace IH := (IH E).left N1 N2
      simp_all
    . intro N
      cases N
