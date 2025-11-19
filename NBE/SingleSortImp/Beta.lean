import NBE.SingleSortImp.Term

namespace SingleSortImp
/-!
### beta_equalities between Morphisms
-/


inductive Tm.beta_step: Tm -> Tm -> Prop where
  -- beta reduction
  | appAbs {t s: Tm}: Tm.beta_step (.app t.abs s) (t.subst 0 s.up0).down0
  -- congrunence relation
  | abs {t1 t2: Tm}: Tm.beta_step t1 t2 -> Tm.beta_step t1.abs t2.abs
  | app1 {t1 t2 s: Tm}: Tm.beta_step t1 t2 -> Tm.beta_step (.app t1 s) (.app t2 s)
  | app2 {t s1 s2: Tm}: Tm.beta_step s1 s2 -> Tm.beta_step (.app t s1) (.app t s2)


def Tm.beta_mstep: Tm -> Tm -> Prop := RTCl Tm.beta_step
def Tm.beta_eq := ECl Tm.beta_step
def Tm.normal := Relation.Normal Tm.beta_step


theorem Tm.beta_mstep.abs {t1 t2: Tm}:
  t1.beta_mstep t2 -> t1.abs.beta_mstep t2.abs
:= by
  apply RTCl.keep_cong Tm.beta_step.abs


theorem Tm.beta_mstep.app1 {t1 t2 s: Tm}:
  t1.beta_mstep t2 -> (t1.app s).beta_mstep (t2.app s)
:= by
  apply RTCl.keep_cong Tm.beta_step.app1


theorem Tm.beta_mstep.app2 {t s1 s2: Tm}:
  s1.beta_mstep s2 -> (t.app s1).beta_mstep (t.app s2)
:= by
  apply RTCl.keep_cong Tm.beta_step.app2


theorem Tm.beta_mstep.app {t1 t2 s1 s2: Tm}:
  t1.beta_mstep t2 ->
  s1.beta_mstep s2 ->
  (t1.app s1).beta_mstep (t2.app s2)
:= by
  intro St Ss
  apply RTCl.trans
  . apply Tm.beta_mstep.app1
    exact St
  . apply Tm.beta_mstep.app2
    exact Ss


theorem Tm.beta_eq.abs {t1 t2: Tm}:
  t1.beta_eq t2 -> t1.abs.beta_eq t2.abs
:= by
  apply ECl.keep_cong Tm.beta_step.abs


theorem Tm.beta_eq.app1 {t1 t2 s: Tm}:
  t1.beta_eq t2 -> (t1.app s).beta_eq (t2.app s)
:= by
  apply ECl.keep_cong Tm.beta_step.app1


theorem Tm.beta_eq.app2 {t s1 s2: Tm}:
  s1.beta_eq s2 -> (t.app s1).beta_eq (t.app s2)
:= by
  apply ECl.keep_cong Tm.beta_step.app2


mutual
  inductive Tm.BNE: Tm -> Prop where
    | var {x}: Tm.BNE (.var x)
    | app {s t}: Tm.BNE s -> Tm.BNF t -> Tm.BNE (s.app t)

  inductive Tm.BNF: Tm -> Prop where
    | neutral {t}: Tm.BNE t -> Tm.BNF t
    | abs {t}: Tm.BNF t -> Tm.BNF t.abs
end


theorem Tm.BNF.normal {t: Tm}:
  t.BNF -> t.normal
:= by
  intro H
  intro ⟨t', S⟩
  induction t generalizing t' with
  | var x =>
    cases S
  | app t1 t2 IH1 IH2 =>
    cases H with | neutral H =>
    cases H with | app H1 H2 =>
    have H: t1.BNF := by constructor; assumption
    cases S with
    | appAbs =>
      cases H1
    | app1 =>
      apply IH1 H
      assumption
    | app2 =>
      apply IH2 H2
      assumption
  | abs M IH =>
    cases H with
    | neutral H =>
      cases H
    | abs H =>
      specialize IH H
      cases S
      apply IH
      assumption


theorem Tm.normal.BNF {t: Tm}:
  t.normal -> t.BNF
:= by
  intro H
  induction t with
  | var x =>
    constructor
    constructor
  | app t1 t2 IH1 IH2 =>
    have N1: t1.normal := by
      intro ⟨y, S⟩
      apply H
      exists y.app t2
      apply beta_step.app1
      exact S
    replace IH1 := IH1 N1
    have N2: t2.normal := by
      intro ⟨y, S⟩
      apply H
      exists t1.app y
      apply beta_step.app2
      exact S
    replace IH2 := IH2 N2
    constructor
    constructor
    . cases IH1 with
      | neutral =>
        assumption
      | abs N =>
        exfalso
        apply H
        constructor
        constructor
    . exact IH2
  | abs t IH =>
    apply BNF.abs
    apply IH
    intro ⟨y, S⟩
    apply H
    constructor
    apply beta_step.abs
    exact S


theorem Tm.beta_step.typing {Γ: Context} {t t': Tm} {T}:
  t.beta_step t' -> Γ.Typing t T -> Γ.Typing t' T
:= by
  intro S HT
  induction HT generalizing t' with
  | var H =>
    cases S
  | abs H IH =>
    cases S with | abs S =>
    specialize IH S
    constructor
    exact IH
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



theorem Tm.BN_up {t: Tm} {c n}:
  (t.BNE <-> (t.up c n).BNE) ∧ (t.BNF <-> (t.up c n).BNF)
:= by
  induction t generalizing c n <;> grind [Tm.BNF, Tm.BNE, up]


theorem Tm.BNE.up {t: Tm} {c n}:
  t.BNE -> (t.up c n).BNE
:= by
  apply Tm.BN_up.left.mp


theorem Tm.BNE.up_inv {t: Tm} {c n}:
  (t.up c n).BNE -> t.BNE
:= by
  apply Tm.BN_up.left.mpr


theorem Tm.BNF.up {t: Tm} {c n}:
  t.BNF -> (t.up c n).BNF
:= by
  apply Tm.BN_up.right.mp


theorem Tm.BNF.up_inv {t: Tm} {c n}:
  (t.up c n).BNF -> t.BNF
:= by
  apply Tm.BN_up.right.mpr


theorem Tm.BN_down {t: Tm} {c}:
  (t.BNE <-> (t.down c).BNE) ∧ (t.BNF <-> (t.down c).BNF)
:= by
  induction t generalizing c <;> grind [Tm.BNF, Tm.BNE, down]


theorem Tm.BNE.down {t: Tm} {c}:
  t.BNE -> (t.down c).BNE
:= by
  apply Tm.BN_down.left.mp


theorem Tm.BNE.down_inv {t: Tm} {c}:
  (t.down c).BNE -> t.BNE
:= by
  apply Tm.BN_down.left.mpr


theorem Tm.BNF.down {t: Tm} {c}:
  t.BNF -> (t.down c).BNF
:= by
  apply Tm.BN_down.right.mp


/-!
We know some facts about reduction. We first need the following lemma to perform a
`beta_step` operation.
-/

/--
This is trivial, but there could be some situation that the `t` is not `beta_step` to a
substitution. Then, you can apply this theorem to intro the `t'` in order to do the computation.
-/
theorem Tm.beta_step.compute {t t' t'': Tm}:
  t.beta_step t' -> t' = t'' -> t.beta_step t''
:= by
  intro H E
  simp_all


theorem Tm.beta_step.appAbs_ssubst {t s: Tm}:
  (t.abs.app s).beta_step (t.ssubst (.step s))
:= by
  apply Tm.beta_step.compute
  . apply Tm.beta_step.appAbs
  . apply Tm.step_ssubst


theorem Tm.beta_step.ssubst {t1 t2: Tm} {s: Subst}:
  t1.beta_step t2 ->
  (t1.ssubst s).beta_step (t2.ssubst s)
:= by
  intro S
  induction S generalizing s with
  | appAbs =>
    rename_i t11 t12
    rewrite [Tm.step_ssubst]
    simp [Tm.ssubst]
    apply Tm.beta_step.compute
    . apply Tm.beta_step.appAbs_ssubst
    simp
    apply Tm.ssubst_congr
    intro n
    simp [Subst.comp]
    cases n with
    | zero =>
      simp [Subst.step, Subst.abs, Tm.ssubst]
    | succ m =>
      simp [Subst.step, Subst.abs, Tm.ssubst]
  | abs S IH=>
    constructor
    apply IH
  | app1 S IH =>
    apply Tm.beta_step.app1
    apply IH
  | app2 S IH =>
    apply Tm.beta_step.app2
    apply IH


/--
The shift is congruent over `beta_step`
-/
theorem Tm.beta_step.up {c n} {t t': Tm}:
  t.beta_step t' -> (t.up c n).beta_step (t'.up c n)
:= by
  simp [Tm.up_ssubst]
  apply Tm.beta_step.ssubst


theorem Tm.beta_eq.up {c n} {t t': Tm}:
  t.beta_eq t' -> (t.up c n).beta_eq (t'.up c n)
:= by
  intro S
  apply ECl.keep_cong Tm.beta_step.up
  exact S


theorem Tm.beta_step.down {c} {t t': Tm}:
  t.beta_step t' -> (t.down c).beta_step (t'.down c)
:= by
  simp [Tm.down_ssubst]
  apply Tm.beta_step.ssubst


theorem Tm.beta_mstep.down {c} {t t': Tm}:
  t.beta_mstep t' -> (t.down c).beta_mstep (t'.down c)
:= by
  apply RTCl.keep_cong Tm.beta_step.down


theorem Tm.beta_eq.down {c} {t t': Tm}:
  t.beta_eq t' -> (t.down c).beta_eq (t'.down c)
:= by
  apply ECl.keep_cong Tm.beta_step.down


theorem Tm.beta_mstep.up_down {t t': Tm}:
  t.up0.beta_mstep t' -> t.beta_mstep t'.down0
:= by
  intro H
  replace H := Tm.beta_mstep.down H (c := 0)
  simp [Tm.up0] at H
  exact H


/--
Parallel evaluation.
-/
def Tm.eval: Tm -> Tm
  | .var x => .var x
  | .abs t => .abs t.eval
  | .app (.abs t1) t2 =>
    (t1.eval.subst 0 t2.eval.up0).down0
  | .app t1 t2 =>
    .app t1.eval t2.eval


theorem Tm.eval_rename {t: Tm} {a: Rename}:
  (t.rename a).eval = t.eval.rename a
:= by
  induction t generalizing a with
  | var x =>
    simp [eval, rename]
  | abs t IH =>
    simp [eval, rename]
    apply IH
  | app t1 t2 IH1 IH2 =>
    cases t1 with
    | var x =>
      simp [eval, rename]
      apply IH2
    | app s1 s2 =>
      simp [eval, rename]
      solve_by_elim
    | abs t1 =>
      simp [eval, rename] at *
      simp [IH1, IH2]
      generalize t1.eval = t1
      generalize t2.eval = t2
      simp [Tm.step_ssubst]
      congr
      funext n
      cases n with
      | zero =>
        simp [Subst.rename, Subst.step, Rename.subst, Rename.abs]
      | succ =>
        simp [Subst.rename, Subst.step, Rename.subst, Rename.abs, Tm.rename]


@[simp]
theorem Tm.eval_up {t: Tm}:
  t.up0.eval = t.eval.up0
:= by
  unfold up0
  simp [Tm.up_rename, Tm.eval_rename]


/--
The parallel reduction relation.
-/
inductive Tm.beta_step2: Tm -> Tm -> Prop where
  -- beta reduction
  | appAbs {t1 t2 s1 s2: Tm}: t1.beta_step2 t2 -> s1.beta_step2 s2 -> Tm.beta_step2 (.app t1.abs s1) (t2.subst 0 s2.up0).down0
  -- congrunence relation
  | abs {t1 t2: Tm}: Tm.beta_step2 t1 t2 -> Tm.beta_step2 t1.abs t2.abs
  | app {t1 t2 s1 s2: Tm}: Tm.beta_step2 t1 t2 -> Tm.beta_step2 s1 s2 -> Tm.beta_step2 (.app t1 s1) (.app t2 s2)
  -- refl
  | var {x: Nat}: Tm.beta_step2 (.var x) (.var x)


theorem Tm.beta_step2.refl {t: Tm}:
  t.beta_step2 t
:= by
  induction t <;> grind [beta_step2]


theorem Tm.beta_step2.app1 {t1 t2 s: Tm}:
  t1.beta_step2 t2 ->
  (t1.app s).beta_step2 (t2.app s)
:= by
  intro S
  apply app
  . exact S
  . apply refl


theorem Tm.beta_step2.app2 {t s1 s2: Tm}:
  s1.beta_step2 s2 ->
  (t.app s1).beta_step2 (t.app s2)
:= by
  intro S
  apply app
  . apply refl
  . exact S


theorem Tm.beta_step.beta_step2 {t1 t2: Tm}:
  t1.beta_step t2 -> t1.beta_step2 t2
:= by
  intro S
  induction S with
  | appAbs =>
    apply beta_step2.appAbs .refl .refl
  | abs S IH =>
    apply beta_step2.abs
    apply IH
  | app1 S IH =>
    apply beta_step2.app1
    exact IH
  | app2 S IH =>
    apply beta_step2.app2
    exact IH


theorem Tm.beta_step2.beta_mstep {t1 t2: Tm}:
  t1.beta_step2 t2 -> t1.beta_mstep t2
:= by
  intro S
  induction S with
  | var =>
    apply RTCl.refl
  | appAbs S1 S2 IH1 IH2 =>
    apply RTCl.trans
    . apply Tm.beta_mstep.app1
      apply Tm.beta_mstep.abs
      apply IH1
    apply RTCl.trans
    . apply Tm.beta_mstep.app2
      apply IH2
    apply RTCl.inclusion
    apply beta_step.appAbs
  | abs S IH =>
    apply beta_mstep.abs
    exact IH
  | app S1 S2 IH1 IH2 =>
    apply beta_mstep.app
    . apply IH1
    . apply IH2


theorem Tm.beta_step2_eval {t: Tm}:
  t.beta_step2 t.eval
:= by
  induction t with
  | var x =>
    simp [eval]
    apply beta_step2.refl
  | abs t IH =>
    simp [eval]
    apply beta_step2.abs
    apply IH
  | app t1 t2 IH1 IH2 =>
    cases t1 with
    | var x =>
      simp [eval]
      apply beta_step2.app2
      exact IH2
    | app s1 s2 =>
      simp [eval]
      apply beta_step2.app
      . apply IH1
      . apply IH2
    | abs t1 =>
      simp [eval] at *
      apply beta_step2.appAbs
      . generalize E: t1.eval.abs = t1' at IH1
        cases IH1 with
        | abs =>
          cases E
          assumption
      . apply IH2


theorem Tm.beta_step2.compute {t t' t'': Tm}:
  t.beta_step2 t' -> t' = t'' -> t.beta_step2 t''
:= by
  intro H E
  simp_all


theorem Tm.beta_step2.ssubst {t1 t2: Tm} {s: Subst}:
  t1.beta_step2 t2 ->
  (t1.ssubst s).beta_step2 (t2.ssubst s)
:= by
  intro S
  induction S generalizing s with
  | var =>
    apply beta_step2.refl
  | abs S IH =>
    simp [Tm.ssubst]
    apply beta_step2.abs
    apply IH
  | app S1 S2 IH1 IH2 =>
    simp [Tm.ssubst]
    apply beta_step2.app
    . apply IH1
    . apply IH2
  | appAbs S1 S2 IH1 IH2 =>
    simp [Tm.ssubst]
    apply Tm.beta_step2.compute
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


theorem Tm.beta_step2.subst1 {t1 t2 s: Tm} {i}:
  t1.beta_step2 t2 ->
  (t1.subst i s).beta_step2 (t2.subst i s)
:= by
  simp [Tm.subst_ssubst]
  apply Tm.beta_step2.ssubst


theorem Tm.beta_step2.up {t1 t2: Tm} {c n}:
  t1.beta_step2 t2 -> (t1.up c n).beta_step2 (t2.up c n)
:= by
  simp [Tm.up_ssubst]
  apply Tm.beta_step2.ssubst


theorem Tm.beta_step2.down {t1 t2: Tm} {c}:
  t1.beta_step2 t2 -> (t1.down c).beta_step2 (t2.down c )
:= by
  simp [Tm.down_ssubst]
  apply Tm.beta_step2.ssubst


theorem Tm.beta_step2.subst2 {t s1 s2: Tm} {i}:
  s1.beta_step2 s2 ->
  (t.subst i s1).beta_step2 (t.subst i s2)
:= by
  intro S
  induction t generalizing i s1 s2 with
  | var x =>
    simp [Tm.subst]
    split
    . exact S
    . apply beta_step2.refl
  | abs t IH =>
    simp [Tm.subst]
    apply beta_step2.abs
    apply IH
    apply S.up
  | app t1 t2 IH1 IH2 =>
    simp [Tm.subst]
    apply Tm.beta_step2.app
    . apply IH1
      exact S
    . apply IH2
      exact S


theorem Tm.beta_step2.subst {t1 t2 s1 s2: Tm} {i}:
  t1.beta_step2 t2 ->
  s1.beta_step2 s2 ->
  (t1.subst i s1).beta_step2 (t2.subst i s2)
:= by
  intro S1 S2
  induction S1 generalizing i s1 s2 with
  | var =>
    apply beta_step2.subst2
    exact S2
  | abs S IH =>
    simp [Tm.subst]
    apply beta_step2.abs
    apply IH
    apply S2.up
  | app _ _ IH1 IH2 =>
    simp [Tm.subst]
    apply beta_step2.app
    . apply IH1
      exact S2
    . apply IH2
      exact S2
  | appAbs _ _ IH1 IH2 =>
    simp [Tm.subst]
    apply beta_step2.compute
    . apply beta_step2.appAbs
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
        cases n with
        | zero =>
          simp [Subst.id, Tm.ssubst, Subst.step, Subst.comp, Subst.up]
        | succ =>
          simp [Subst.id, Tm.ssubst, Subst.step, Subst.comp, Subst.up]
      . simp [Tm.ssubst, Subst.step]


theorem Tm.beta_step2.switch {t1 t2: Tm}:
  t1.beta_step2 t2 ->
  t2.beta_step2 t1.eval
:= by
  intro S
  induction S with
  | var =>
    apply Tm.beta_step2_eval
  | abs S IH =>
    simp [eval]
    apply beta_step2.abs
    apply IH
  | appAbs =>
    simp [eval]
    apply Tm.beta_step2.down
    apply Tm.beta_step2.subst
    . assumption
    . apply Tm.beta_step2.up
      assumption
  | app S1 S2 IH1 IH2 =>
    rename_i t1 t2 s1 s2
    cases t1 with
    | var =>
      simp [eval] at *
      apply beta_step2.app
      . exact IH1
      . exact IH2
    | app =>
      simp [eval] at *
      apply beta_step2.app
      . exact IH1
      . exact IH2
    | abs t1 =>
      simp [eval] at *
      generalize E: t1.eval.abs = t1' at IH1
      cases S1 with
      | abs S1 =>
        cases IH1 with
        | abs IH1 =>
          simp_all
          apply beta_step2.appAbs
          . apply IH1
          . apply IH2


theorem Tm.beta_step2.eval {t1 t2: Tm}:
  t1.beta_step2 t2 ->
  t1.eval.beta_step2 t2.eval
:= by
  intro S
  replace S := S.switch
  apply S.switch


theorem Tm.beta_mstep.eval {t1 t2: Tm}:
  t1.beta_mstep t2 -> t1.eval.beta_mstep t2.eval
:= by
  intro S
  induction S with
  | refl =>
    apply RTCl.refl
  | step Hxy Hyz IH =>
    replace Hxy := Hxy.beta_step2
    replace Hxy := Hxy.eval
    replace Hxy := Hxy.beta_mstep
    apply RTCl.trans
    . apply Hxy
    . apply IH


instance Tm.beta_step.semi_confl: SemiConfluent Tm.beta_step where
  semi_confl := by
    intro m1 m2 m3 S MS
    exists m3.eval
    and_intros
    . replace S := S.beta_step2
      replace S := S.switch
      replace S := S.beta_mstep
      apply RTCl.trans
      . apply S
      . apply beta_mstep.eval
        exact MS
    . apply beta_step2.beta_mstep
      apply beta_step2_eval


theorem Tm.beta_eq_normal_beta_mstep {t n: Tm}:
  t.beta_eq n -> n.normal -> t.beta_mstep n
:= by
  intro S N
  obtain ⟨s, Hts, Hsn⟩ := Relation.church_rosser Tm.beta_step S
  have E := N.MNormal Hsn
  cases E
  exact Hts


/-!
### Interpretation in Presheaf
Given a presheaf F, we can turn it into a functor from Tm to PSh(C).
F corresponds to the forcing relation with functoriality corresponding to monotonicity.
Semantic entailment in a Kripke structure is a natural transformation in the presheaf category.
The soundness is the functor from Tm to PSh(C)

We have to explain the following:
1. How to map `imp` given `Atom => F`
2. How to map a `Γ: Context` given its value on `Ty`
3. How to map a term `t` such that `Γ |- M: T` implies `[M]: [Γ] [T]` <- the natural transformation.
-/

def Tm.forces (F: Tm -> Prop) (Γ: Context) (t: Tm) (T: Ty) :=
  match T with
  | .Atom =>
    Γ.Typing t T ∧ exists t', t.beta_eq t' ∧ F t'
  | .imp A B =>
    forall (s: Tm) Γ', forces F (Γ' ++ Γ) s A -> forces F (Γ' ++ Γ) ((t.up 0 Γ'.length).app s) B


theorem Tm.BNF.forces_app {Γ' Γ t T}:
  forces Tm.BNF Γ t T -> forces Tm.BNF (Γ' ++ Γ) (t.up 0 Γ'.length) T
:= by
  intro H
  induction T generalizing Γ' with
  | Atom =>
    simp [forces] at *
    and_intros
    . apply Context.weaken_app
      exact H.left
    . obtain ⟨t', S, N⟩ := H.right
      exists t'.up 0 Γ'.length
      and_intros
      . apply Tm.beta_eq.up
        exact S
      . apply N.up
  | imp T1 T2 IH1 IH2 =>
    simp [forces] at *
    intro s Γ'' F
    simp [Tm.shift_up_add]
    rewrite [<-List.append_assoc]
    rewrite [Nat.add_comm]
    rewrite [<-List.length_append]
    apply H
    simp
    exact F


theorem Tm.BNF.app1_inv {t s: Tm}:
  (t.app s).BNF -> t.BNF
:= by
  grind [BNE, BNF]


theorem Tm.abs_up_app_beta_step {t: Tm}:
  (t.abs.up0.app (.var 0)).beta_step t
:= by
  simp [up0, up]
  apply Tm.beta_step.compute Tm.beta_step.appAbs_ssubst
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


theorem Tm.beta_mstep_app_var_normal' {t s: Tm}:
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
    . apply N.app1_inv
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
        . apply Tm.abs_up_app_beta_step
        apply ECl.refl

      have S3: M.abs.down0.beta_eq s.abs := by
        simp [down0, down]
        apply Tm.beta_eq.abs
        apply ECl.trans
        . apply ECl.symm
          exact S2
        . exact S1

      rewrite [Tm.subst_up_down_var0] at Hyz
      exists s.abs.up0
      have N: s.abs.up0.BNF := by
        apply BNF.up
        apply BNF.abs
        apply N
      and_intros
      . apply Tm.beta_eq_normal_beta_mstep _ N.normal
        apply ECl.trans
        . exact I
        apply Tm.beta_eq.up
        exact S3
      . exact N


theorem Tm.beta_mstep_app_var_normal {t s: Tm}:
  ((t.up0.app (.var 0)).beta_mstep s) -> s.BNF -> exists t', t.beta_eq t' ∧ t'.BNF
:= by
  intro S N
  have E: t.up0.beta_eq (t.up0.down0.up0) := by simp; apply ECl.refl
  obtain ⟨s, S, N⟩ := Tm.beta_mstep_app_var_normal' E S N
  exists s.down0
  and_intros
  . apply RTCl.sub_ecl
    apply Tm.beta_mstep.up_down
    exact S
  . apply N.down


theorem completeness {Γ T}:
  (forall {t}, Tm.forces Tm.BNF Γ t T -> Γ.Typing t T ∧ exists t', t.beta_eq t' ∧ Tm.BNF t') ∧
  (forall {t}, (Γ.Typing t T ∧ exists t', t.beta_eq t' ∧ Tm.BNE t') -> Tm.forces Tm.BNF Γ t T)
:= by
  induction T generalizing Γ with
  | Atom =>
    and_intros
    . intro t F
      simp [Tm.forces] at F
      exact F
    . intro t ⟨HT, t', S, N⟩
      simp [Tm.forces]
      simp_all
      exists t'
      simp_all
      apply Tm.BNF.neutral
      assumption
  | imp A B IHA IHB =>
    and_intros
    . intro t HF
      simp [Tm.forces] at HF
      have H: Tm.forces Tm.BNF ([A] ++ Γ) (.var 0) A := by
        apply IHA.right
        and_intros
        . constructor
          simp_all
        . exists (.var 0)
          and_intros
          . apply ECl.refl
          . constructor
      specialize HF _ _ H
      simp at *
      replace IHB := IHB.left HF
      obtain ⟨HT, t', S, N⟩ := IHB
      and_intros
      . cases HT with | app H1 H2 =>
        cases H2
        simp_all
        apply Context.weaken_cons_inv
        assumption
      . clear H
        have H := Tm.beta_eq_normal_beta_mstep S N.normal
        clear S IHA HF
        apply Tm.beta_mstep_app_var_normal
        . exact H
        . exact N
    . intro t ⟨HT, t', S, N⟩
      simp [Tm.forces]
      intro s Γ' HF
      replace IHA := IHA.left HF
      apply IHB.right
      and_intros
      . constructor
        . apply Context.weaken_app
          exact HT
        . apply IHA.left
      . obtain ⟨s', S', N'⟩ := IHA.right
        exists (t'.up 0 Γ'.length).app s'
        and_intros
        . apply ECl.trans
          . apply Tm.beta_eq.app1
            apply Tm.beta_eq.up
            exact S
          . apply Tm.beta_eq.app2
            exact S'
        . apply Tm.BNE.app
          . apply N.up
          . exact N'


abbrev Env := FinMap Tm

def Env.up (c n: Nat): Env -> Env
  | [] => []
  | x :: xs => (x.up c n) :: (up c n xs)


@[simp]
theorem Env.up_length_beta_eq {e: Env} {c n}:
  (e.up c n).length = e.length
:= by
  induction e <;>
  . simp_all [Env.up]


theorem Env.up_index_lt {e: Env} {c n} {i: Nat}:
  (h: i < e.length) ->
  (e.up c n)[i]'(by simp_all) = e[i].up c n
:= by
  intro H
  induction i generalizing e with
  | zero =>
    cases e with
    | nil =>
      cases H
    | cons t ts =>
      simp [up]
  | succ i IH =>
    cases e with
    | nil =>
      cases H
    | cons t ts =>
      simp [up] at *
      apply IH


def Tm.msubst_var: Env -> Nat -> Tm
  | e, n => FinMap.lookupD n (.var n) e


@[simp]
theorem Tm.msubst_var_nil {n: Nat}:
  Tm.msubst_var [] n = (.var n)
:= by
  simp [msubst_var]


@[simp]
theorem Tm.msubst_var_zero {e: Env} {t: Tm}:
  Tm.msubst_var (t :: e) 0 = t
:= by
  simp [msubst_var]


theorem Tm.msubst_var_lt {e: Env} {n: Nat}:
  (h: n < e.length) ->
  msubst_var e n = e[n]'h
:= by
  intro H
  unfold msubst_var
  simp [FinMap.lookupD_lt H]


theorem Tm.msubst_var_ge {e: Env} {n: Nat}:
  (h: n ≥ e.length) ->
  msubst_var e n = var n
:= by
  intro H
  unfold msubst_var
  simp [FinMap.lookupD_ge H]


@[simp]
theorem Tm.msubst_var_succ {e: Env} {t} {n: Nat}:
  msubst_var (t :: e.up 0 1) (n + 1) = (msubst_var e n).up0
:= by
  simp [msubst_var, up0]
  rewrite [<-Tm.var_up]
  generalize (var n) = s
  unfold Tm.up0
  induction n generalizing e with
  | zero =>
    cases e with
    | nil =>
      simp [Env.up]
    | cons =>
      simp [Env.up]
  | succ m IH =>
    cases e with
    | nil =>
      simp [Env.up]
    | cons =>
      simp [Env.up]
      apply IH


def Tm.msubst (s: Env) (t: Tm): Tm :=
  match t with
  | .var x => Tm.msubst_var s x
  | .abs M => .abs $ M.msubst $ (Tm.var 0) :: s.up 0 1
  | .app M N => .app (M.msubst s) (N.msubst s)


def Env.subst (e: Env): Subst := Tm.msubst_var e

theorem Tm.msubst_ssubst {e: Env} {t: Tm}:
  t.msubst e = t.ssubst e.subst
:= by
  unfold Env.subst
  induction t generalizing e with
  | var x =>
    simp [msubst, ssubst]
  | app =>
    simp [msubst, ssubst]
    solve_by_elim
  | abs M IH =>
    simp [msubst, ssubst]
    rewrite [IH]
    congr
    funext n
    cases n with
    | zero =>
      simp [Subst.abs]
    | succ m =>
      simp [Subst.abs]


def Env.vars: Nat -> Env
  | 0 => []
  | n + 1 => (Tm.var 0) :: (vars n).up 0 1


@[simp]
theorem Env.vars_id {n: Nat}:
  (Env.vars n).subst = Subst.id
:= by
  unfold subst
  funext i
  cases n with
  | zero =>
    simp [Env.vars, Subst.id]
  | succ n =>
    induction i generalizing n with
    | zero =>
      simp [Env.vars, Subst.id]
    | succ i IH =>
      simp [Env.vars, Subst.id]
      cases n with
      | zero =>
        simp [Env.vars]
      | succ n =>
        rewrite [IH]
        simp [Subst.id]


@[simp]
theorem Tm.msubst_vars {n} {t: Tm}:
  t.msubst (Env.vars n) = t
:= by
  simp [Tm.msubst_ssubst]
  simp [<-Tm.ssubst_id]


@[simp]
theorem Tm.msubst_nil {t: Tm}:
  t.msubst [] = t
:= by
  apply Tm.msubst_vars (n := 0)



inductive Instantiate (Δ: Context): Env -> Context -> Prop where
  | nil: Instantiate Δ [] []
  | cons {T: Ty} {t: Tm} {Γ ts}:
    Tm.forces Tm.BNF Δ t T ->
    Instantiate Δ ts Γ ->
    Instantiate Δ (t :: ts) (T :: Γ)



theorem Instantiate.weaken {Δ Δ': Context} {Γ env}:
  Instantiate Δ env Γ -> Instantiate (Δ' ++ Δ) (env.up 0 Δ'.length) Γ
:= by
  intro I
  induction I with
  | nil =>
    constructor
  | cons F I IH =>
    constructor
    . apply Tm.BNF.forces_app
      exact F
    . exact IH


theorem Instantiate.weaken_cons {Δ: Context} {Γ A env}:
  Instantiate Δ env Γ -> Instantiate (A :: Δ) (env.up 0 1) Γ
:= by
  intro H
  replace H := weaken H (Δ' := [A])
  simp at H
  exact H


@[simp]
theorem Instantiate.self {Γ}:
  Instantiate Γ (Env.vars Γ.length) Γ
:= by
  induction Γ with
  | nil =>
    simp [Env.vars]
    constructor
  | cons T TS IH =>
    apply cons
    . apply completeness.right
      and_intros
      . constructor
        simp
      . exists (.var 0)
        and_intros
        . apply ECl.refl
        . constructor
    . apply weaken_cons
      exact IH


theorem Instantiate.length {Δ Γ: Context} {env: Env}:
  Instantiate Δ env Γ -> env.length = Γ.length
:= by
  intro H
  induction H with
  | nil =>
    simp
  | cons =>
    simp_all


theorem Instantiate.index {Δ: Context} {Γ env} (I: Instantiate Δ env Γ) (i: Nat):
  (h: i < Γ.length) ->
  Tm.forces Tm.BNF Δ (env[i]'(by simp_all [I.length])) Γ[i]
:= by
  intro H
  induction I generalizing i with
  | nil =>
    cases H
  | cons F I IH =>
    cases i with
    | zero =>
      simp
      exact F
    | succ =>
      simp
      apply IH


/--
One part needed for the well-definedness of the natural transformation.
-/
theorem Instantiate.typing {Δ Γ: Context} {env t T}:
  Γ.Typing t T ->
  Instantiate Δ env Γ ->
  Δ.Typing (t.msubst env) T
:= by
  intro HT I
  induction HT generalizing Δ env with
  | var H =>
    rename_i Γ x T
    have L1: x < Γ.length := by
      simp_all [FinMap.lookup_some_lt H]
    have L2: x < env.length := by
      simp_all [I.length]
    simp [Tm.msubst]
    simp [Tm.msubst_var_lt L2]
    have F := I.index x L1
    rewrite [FinMap.lookup_lt_some L1] at H
    simp_all
    replace F := completeness.left F
    apply F.left
  | app H1 H2 IH1 IH2 =>
    simp [Tm.msubst]
    constructor
    . apply IH1
      exact I
    . apply IH2
      exact I
  | abs H IH =>
    rename_i Γ M T1 T2
    simp [Tm.msubst]
    constructor
    apply IH
    constructor
    . apply completeness.right
      and_intros
      . constructor
        simp
      . exists (.var 0)
        and_intros
        . apply ECl.refl
        . constructor
    . apply Instantiate.weaken_cons
      exact I


theorem Tm.beta_step.forces {Γ} {t t': Tm} {T}:
  t.beta_step t' ->
  forces Tm.BNF Γ t T ->
  forces Tm.BNF Γ t' T
:= by
  intro S F
  induction T generalizing Γ t t' with
  | Atom =>
    simp [Tm.forces] at *
    and_intros
    . apply Tm.beta_step.typing
      . exact S
      . apply F.left
    . obtain ⟨t'', S', N⟩ := F.right
      exists t''
      and_intros
      . apply ECl.trans
        . symm
          apply ECl.inclusion
          exact S
        . exact S'
      . exact N
  | imp T1 T2 IH1 IH2 =>
    simp [Tm.forces] at *
    intro s Γ' F'
    apply IH2
    . apply Tm.beta_step.app1
      apply Tm.beta_step.up
      exact S
    . apply F
      exact F'


theorem Tm.beta_step.forces' {Γ: Context} {t t': Tm} {T}:
  Γ.Typing t T ->
  t.beta_step t' ->
  Tm.forces Tm.BNF Γ t' T ->
  Tm.forces Tm.BNF Γ t T
:= by
  intro HT S F
  induction T generalizing Γ t t' with
  | Atom =>
    simp [Tm.forces] at *
    and_intros
    . exact HT
    . obtain ⟨t'', S', N⟩ := F.right
      exists t''
      and_intros
      . apply ECl.step
        . exact S
        . exact S'
      . exact N
  | imp T1 T2 IH1 IH2 =>
    simp [Tm.forces] at *
    intro s Γ' F'
    apply IH2
    . constructor
      . apply Context.weaken_app
        exact HT
      . replace F' := completeness.left F'
        apply F'.left
    . apply Tm.beta_step.app1
      apply Tm.beta_step.up
      exact S
    . apply F
      exact F'


theorem Tm.beta_mstep.forces' {Γ: Context} {t t': Tm} {T}:
  Γ.Typing t T ->
  t.beta_mstep t' ->
  Tm.forces Tm.BNF Γ t' T ->
  Tm.forces Tm.BNF Γ t T
:= by
  intro HT S F
  induction S with
  | refl =>
    assumption
  | step Hxy Hyz IH =>
    apply Tm.beta_step.forces' HT Hxy
    apply IH (Hxy.typing HT)
    exact F


/--
The natural transformation, i.e., the logical entailment.
Each `Γ` and `T` is an object with the term a morphism between them.
If `Γ` and `T` are interpreted as presheaves `[Γ]` and `[T]`, then the morphism
`Γ |- t: T` is interpreted as a natural transformation from `[Γ]` to `[T]`.
That is, for each `Δ` in the category `Context`, you have to find a function from `[Γ](Δ)` to `[T](Δ)`.
The former is those `Δ ⊩ env: Γ`, and the later is `Δ ⊩ t/env: T`
-/
theorem soundness {Γ: Context} {t T}:
  Γ.Typing t T ->
  forall Δ env, Instantiate Δ env Γ -> Tm.forces Tm.BNF Δ (t.msubst env) T
:= by
  intro HT Δ env I
  induction HT generalizing Δ env with
  | var H =>
    rename_i Γ x t
    induction I generalizing x t with
    | nil =>
      cases H
    | cons F I IH =>
      cases x with
      | zero =>
        simp at H
        simp_all [Tm.msubst, Tm.msubst_var]
      | succ y =>
        simp at H
        specialize IH H
        rename_i s Γ ts
        have I: y < ts.length := by
          rewrite [I.length]
          apply FinMap.lookup_some_lt
          exact H
        simp [Tm.msubst] at *
        simp [Tm.msubst_var_lt I] at IH
        have I: y + 1 < (s :: ts).length := by simp_all
        simp [Tm.msubst_var_lt I]
        exact IH
  | app HT1 HT2 IH1 IH2 =>
    specialize IH1 _ _ I
    specialize IH2 _ _ I
    simp [Tm.msubst]
    simp [Tm.forces] at IH1
    replace IH1 := IH1 (Γ' := [])
    simp at IH1
    apply IH1
    exact IH2
  | abs H IH =>
    rename_i Γ M T1 T2
    simp [Tm.forces]
    intro s Δ' F
    obtain ⟨HT, s', Ss, Ns⟩ := completeness.left F
    have K: Instantiate (Δ' ++ Δ) (s :: env.up 0 Δ'.length) (T1 :: Γ) := by
      apply Instantiate.cons
      . exact F
      . apply Instantiate.weaken
        exact I
    specialize IH _ _ K
    apply Tm.beta_mstep.forces' _ _ IH
    . -- typing
      constructor
      . apply Context.weaken_app
        apply Instantiate.typing
        . constructor
          apply H
        . exact I
      . exact HT
    . -- reduction
      simp [Tm.up, Tm.msubst]
      apply RTCl.inclusion
      apply Tm.beta_step.compute
      apply Tm.beta_step.appAbs_ssubst
      generalize Δ'.length = n
      simp [Tm.msubst_ssubst, Tm.up_ssubst]
      -- we then only have to prove the `Subst`s are the same for those under the length of `var`
      clear F s' Ss Ns K IH HT Δ' t T
      apply Tm.ssubst_congr_lt
      intro x L
      simp [Subst.comp]
      cases x with
      | zero =>
        simp [Env.subst, Tm.ssubst, Subst.comp, Subst.up, Subst.step]
      | succ x =>
        unfold Env.subst
        replace L: x < env.length := by
          replace H := H.bound
          simp at H
          rewrite [I.length]
          omega
        have E {s c n}: Tm.msubst_var (s :: env.up c n) (x + 1) = (env[x]).up c n := by
            simp [<-Env.up_index_lt]
            apply Tm.msubst_var_lt
            simp
            exact L
        simp [E]
        generalize env[x] = env'
        simp [Tm.up_ssubst]
        -- again, we only have to prove the beta_equality of the `Subst`
        clear H T1 T2 M E L x I env Γ Δ
        congr
        funext x
        cases x with
        | zero =>
          simp [Tm.ssubst, Subst.up, Subst.comp, Subst.step]
          grind
        | succ =>
          simp [Tm.ssubst, Subst.up, Subst.comp, Subst.step]
          grind


/--
This is the result of the real completeness
-/
theorem Tm.halts {Γ: Context} {t T}:
  Γ.Typing t T -> exists t', t.beta_eq t' ∧ t'.BNF
:= by
  intro HT
  let entailment := soundness HT
  specialize entailment Γ (Env.vars Γ.length) Instantiate.self
  simp at entailment
  let F := completeness.left entailment
  apply F.right
