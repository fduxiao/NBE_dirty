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
def Tm.beta_normal := Relation.Normal Tm.beta_step


theorem Tm.beta_step.beta_mstep {t1 t2: Tm}:
  t1.beta_step t2 -> t1.beta_mstep t2
:= by
  apply RTCl.inclusion


@[refl]
theorem Tm.beta_mstep.refl {t: Tm}:
  t.beta_mstep t
:= by
  apply RTCl.refl


theorem Tm.beta_mstep.trans {t1 t2 t3: Tm}:
  t1.beta_mstep t2 -> t2.beta_mstep t3 -> t1.beta_mstep t3
:= by
  apply RTCl.trans


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


theorem Tm.beta_mstep.beta_eq {t1 t2: Tm}:
  t1.beta_mstep t2 -> t1.beta_eq t2
:= by
  apply RTCl.sub_ecl


theorem Tm.beta_step.beta_eq {t1 t2: Tm}:
  t1.beta_step t2 -> t1.beta_eq t2
:= by
  apply ECl.inclusion


theorem Tm.beta_step.beta_eq_rev {t1 t2: Tm}:
  t1.beta_step t2 -> t2.beta_eq t1
:= by
  apply ECl.reverse


@[refl]
theorem Tm.beta_eq.refl {t: Tm}:
  t.beta_eq t
:= by
  apply ECl.refl


@[symm]
theorem Tm.beta_eq.symm {t1 t2: Tm}:
  t1.beta_eq t2 -> t2.beta_eq t1
:= by
  apply ECl.symm


theorem Tm.beta_eq.trans {t1 t2 t3: Tm}:
  t1.beta_eq t2 -> t2.beta_eq t3 -> t1.beta_eq t3
:= by
  apply ECl.trans


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


theorem Tm.beta_eq.app {t1 t2 s1 s2: Tm}:
  t1.beta_eq t2 -> s1.beta_eq s2 -> (t1.app s1).beta_eq (t2.app s2)
:= by
  intro H1 H2
  apply ECl.trans
  . apply Tm.beta_eq.app1
    exact H1
  . apply Tm.beta_eq.app2
    exact H2


mutual
  inductive Tm.BNE: Tm -> Prop where
    | var {x}: Tm.BNE (.var x)
    | app {s t}: Tm.BNE s -> Tm.BNF t -> Tm.BNE (s.app t)

  inductive Tm.BNF: Tm -> Prop where
    | neutral {t}: Tm.BNE t -> Tm.BNF t
    | abs {t}: Tm.BNF t -> Tm.BNF t.abs
end


theorem Tm.BNF.beta_normal {t: Tm}:
  t.BNF -> t.beta_normal
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


theorem Tm.beta_normal.BNF {t: Tm}:
  t.beta_normal -> t.BNF
:= by
  intro H
  induction t with
  | var x =>
    constructor
    constructor
  | app t1 t2 IH1 IH2 =>
    have N1: t1.beta_normal := by
      intro ⟨y, S⟩
      apply H
      exists y.app t2
      apply beta_step.app1
      exact S
    replace IH1 := IH1 N1
    have N2: t2.beta_normal := by
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
Parallel beta_evaluation.
-/
def Tm.beta_eval: Tm -> Tm
  | .var x => .var x
  | .abs t => .abs t.beta_eval
  | .app (.abs t1) t2 =>
    (t1.beta_eval.subst 0 t2.beta_eval.up0).down0
  | .app t1 t2 =>
    .app t1.beta_eval t2.beta_eval


theorem Tm.beta_eval_rename {t: Tm} {a: Rename}:
  (t.rename a).beta_eval = t.beta_eval.rename a
:= by
  induction t generalizing a with
  | var x =>
    simp [beta_eval, rename]
  | abs t IH =>
    simp [beta_eval, rename]
    apply IH
  | app t1 t2 IH1 IH2 =>
    cases t1 with
    | var x =>
      simp [beta_eval, rename]
      apply IH2
    | app s1 s2 =>
      simp [beta_eval, rename]
      solve_by_elim
    | abs t1 =>
      simp [beta_eval, rename] at *
      simp [IH1, IH2]
      generalize t1.beta_eval = t1
      generalize t2.beta_eval = t2
      simp [Tm.step_ssubst]
      congr
      funext n
      cases n with
      | zero =>
        simp [Subst.rename, Subst.step, Rename.subst, Rename.abs]
      | succ =>
        simp [Subst.rename, Subst.step, Rename.subst, Rename.abs, Tm.rename]


@[simp]
theorem Tm.beta_eval_up {t: Tm}:
  t.up0.beta_eval = t.beta_eval.up0
:= by
  unfold up0
  simp [Tm.up_rename, Tm.beta_eval_rename]


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
    rfl
  | appAbs S1 S2 IH1 IH2 =>
    apply Tm.beta_mstep.trans
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


theorem Tm.beta_step2_beta_eval {t: Tm}:
  t.beta_step2 t.beta_eval
:= by
  induction t with
  | var x =>
    simp [beta_eval]
    apply beta_step2.refl
  | abs t IH =>
    simp [beta_eval]
    apply beta_step2.abs
    apply IH
  | app t1 t2 IH1 IH2 =>
    cases t1 with
    | var x =>
      simp [beta_eval]
      apply beta_step2.app2
      exact IH2
    | app s1 s2 =>
      simp [beta_eval]
      apply beta_step2.app
      . apply IH1
      . apply IH2
    | abs t1 =>
      simp [beta_eval] at *
      apply beta_step2.appAbs
      . generalize E: t1.beta_eval.abs = t1' at IH1
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
  t2.beta_step2 t1.beta_eval
:= by
  intro S
  induction S with
  | var =>
    apply Tm.beta_step2_beta_eval
  | abs S IH =>
    simp [beta_eval]
    apply beta_step2.abs
    apply IH
  | appAbs =>
    simp [beta_eval]
    apply Tm.beta_step2.down
    apply Tm.beta_step2.subst
    . assumption
    . apply Tm.beta_step2.up
      assumption
  | app S1 S2 IH1 IH2 =>
    rename_i t1 t2 s1 s2
    cases t1 with
    | var =>
      simp [beta_eval] at *
      apply beta_step2.app
      . exact IH1
      . exact IH2
    | app =>
      simp [beta_eval] at *
      apply beta_step2.app
      . exact IH1
      . exact IH2
    | abs t1 =>
      simp [beta_eval] at *
      generalize E: t1.beta_eval.abs = t1' at IH1
      cases S1 with
      | abs S1 =>
        cases IH1 with
        | abs IH1 =>
          simp_all
          apply beta_step2.appAbs
          . apply IH1
          . apply IH2


theorem Tm.beta_step2.beta_eval {t1 t2: Tm}:
  t1.beta_step2 t2 ->
  t1.beta_eval.beta_step2 t2.beta_eval
:= by
  intro S
  replace S := S.switch
  apply S.switch


theorem Tm.beta_mstep.beta_eval {t1 t2: Tm}:
  t1.beta_mstep t2 -> t1.beta_eval.beta_mstep t2.beta_eval
:= by
  intro S
  induction S with
  | refl =>
    apply RTCl.refl
  | step Hxy Hyz IH =>
    replace Hxy := Hxy.beta_step2
    replace Hxy := Hxy.beta_eval
    replace Hxy := Hxy.beta_mstep
    apply RTCl.trans
    . apply Hxy
    . apply IH


instance Tm.beta_step.semi_confl: SemiConfluent Tm.beta_step where
  semi_confl := by
    intro m1 m2 m3 S MS
    exists m3.beta_eval
    and_intros
    . replace S := S.beta_step2
      replace S := S.switch
      replace S := S.beta_mstep
      apply RTCl.trans
      . apply S
      . apply beta_mstep.beta_eval
        exact MS
    . apply beta_step2.beta_mstep
      apply beta_step2_beta_eval
