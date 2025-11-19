import NBE.SingleSortImp.Term


namespace SingleSortImp

/-!
# Interpretation in Presheaf Category

## Free Contextual CCC
A Contextual CCC is a category C and a full subcategory T such that
1. C has a terminal object.
2. For Γ in C and A in T, we have the product Γ × A.
3. For two A B in T, we have the exponential.

In our case, the C is the category of all `Context`, i.e., `List Ty` with
0. T is made by those `Ty`.
1. terminal object [].
2. `A :: Γ` is the product.
3. Expoentials are `A.imp B`.
4. Morphisms are typable terms up to βη-equality.
We call this category `Tm`.

This is the free Contextual CCC Tm. If we have another contextual (C, T) and some c ∈ C,
we can generate the interpretation from `Tm` to C.


## Presheaf and Forcing
Given a presheaf `P`, we can turn it into a functor from `Tm` to `PSh(C)`.
`P` corresponds to the forcing relation on variables with functoriality corresponding to monotonicity.
Semantic entailment in a Kripke structure is a natural transformation in the presheaf category.
The soundness is the functor  `[·]: Tm → PSh(C)`

We have to explain the following:
1. How to map `imp` when we interpret the atomic type(s) (variables) as a presheaf.
2. How to map a `Γ: Context` given its value on `Ty`
3. How to map a term `t` such that `Γ ⊢ t: T` implies `[M]: [t] [T]` <- the natural transformation.

We model a presheaf as a predicate `Context -> Tm -> Ty -> Prop` with the weakening property, which
means given a type `T`, then it is interpreted as a presheaf on some `Γ` that collecting all terms satisfying
the predicate. Actually, we only need it to be a subset of the typable terms.

Since `imp` is the exponential in the category `Tm`, then `[σ → τ]` must be the expoential `[σ] ⇒ [τ]`,
which is the exponential in the presheaf category. This gives the _forcing_ relation: another functor that
collects certain terms.

This answers the object map on each single `Ty`. For a context `Γ`, which is just a _product_ of types, we interpret it
as a pointwise forcing relation, i.e., `Γ = (T1, T2, T3)` is interpret as a presheaf such that given a `Δ: Context`,
`[Γ](Δ) = (t1, t2, t3)` such taht `Δ ⊩ t1: T1, Δ ⊩ t2: T2, Δ ⊩ t3: T3`. We write this as `Δ ⊩ Γ`.

Thus, `Γ ⊨ t: T` means that forall `Δ ⊩ e: Γ`, we have `Δ ⊩ t[e]: T`. Now, `Γ ⊢ t: T` alsw suggests a natural
transformation `[t]: [Γ] → [T]`: we have the component mapping that given any `Δ`, `[t](Δ): [Γ](Δ) -> [T](Δ)`.
The soundness forces each `e ∈ [Γ](Δ)` mapped `t[e] ∈ [T](Δ)`.
-/

structure Presheaf where
  Pred: Context -> Tm -> Ty -> Prop
  weaken {Γ' Γ: Context} {t: Tm} {T}:
    Pred Γ t T ->
    Pred (Γ' ++ Γ) (t.up 0 Γ'.length) T


instance: CoeFun Presheaf (fun _ => Context -> Tm -> Ty -> Prop) where
  coe P := P.Pred


def forcePred (P: Context -> Tm -> Ty -> Prop) (Γ: Context) (t: Tm) (T: Ty) :=
  match T with
  | .Atom =>
    P Γ t T
  | .imp A B =>
    forall (s: Tm) Γ', forcePred P (Γ' ++ Γ) s A -> forcePred P (Γ' ++ Γ) ((t.up 0 Γ'.length).app s) B


def Presheaf.forces (P: Presheaf): Presheaf where
  Pred := forcePred P
  weaken {Γ' Γ t T} := by
    intro H
    induction T generalizing Γ' with
    | Atom =>
      simp [forcePred] at *
      apply P.weaken H
    | imp T1 T2 IH1 IH2 =>
      simp [forcePred] at *
      intro s Γ'' F
      simp [Tm.shift_up_add]
      rewrite [<-List.append_assoc]
      rewrite [Nat.add_comm]
      rewrite [<-List.length_append]
      apply H
      simp
      exact F


class NPair (PNE: outParam Presheaf) (PNF: Presheaf) where
  atom {Γ t}: PNE Γ t .Atom -> PNF Γ t .Atom
  imp {Γ Γ' t s A B}:
    PNE.Pred Γ t (A.imp B) ->
    PNF.Pred (Γ' ++ Γ) s A ->
    PNE.Pred (Γ' ++ Γ) ((Tm.up 0 (List.length Γ') t).app s) B
  var {Γ A}: PNE ([A] ++ Γ) (Tm.var 0) A
  app_inv {Γ t A B}: PNF.Pred (A :: Γ) ((Tm.up 0 1 t).app (Tm.var 0)) B -> PNF.Pred Γ t (A.imp B)


theorem NPair.completeness {PNE PNF: Presheaf} [inst: NPair PNE PNF] {Γ: Context} {T: Ty}:
  (forall {t}, PNF.forces Γ t T -> PNF Γ t T) ∧
  (forall {t}, PNE Γ t T -> PNF.forces Γ t T)
:= by
  induction T generalizing Γ with
  | Atom =>
    and_intros
    . intro t F
      simp [Presheaf.forces] at F
      exact F
    . intro t F
      simp [Presheaf.forces, forcePred]
      apply inst.atom
      exact F
  | imp A B IHA IHB =>
    and_intros
    . intro t F
      simp [Presheaf.forces, forcePred] at F
      have H: PNF.forces ([A] ++ Γ) (.var 0) A := by
        apply IHA.right
        and_intros
        apply inst.var
      specialize F _ _ H
      simp at *
      replace IHB := IHB.left F
      apply inst.app_inv IHB
    . intro t NE
      simp [Presheaf.forces, forcePred]
      intro s Γ' F
      replace IHA := IHA.left F
      apply IHB.right
      apply inst.imp
      . exact NE
      . exact IHA


/-!
### Natural transformation between presheaves.
-/

/--
We only defined the morphisms from a context `Γ` to a type `T` in the (free) contextual CCC.
Since a context is just a product of those types, a morphism from a context to a context is
a list of terms. This name `Env` comes from _Software Foundations_.
-/
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


/--
The forces relation on a context. The name `Instantiate` is also due to _Software Foundations_
-/
inductive Instantiate (P: Presheaf) (Δ: Context): Env -> Context -> Prop where
  | nil: Instantiate P Δ [] []
  | cons {T: Ty} {t: Tm} {Γ ts}:
    P.forces Δ t T ->
    Instantiate P Δ ts Γ ->
    Instantiate P Δ (t :: ts) (T :: Γ)



theorem Instantiate.weaken {P: Presheaf} {Δ Δ': Context} {Γ env}:
  Instantiate P Δ env Γ -> Instantiate P (Δ' ++ Δ) (env.up 0 Δ'.length) Γ
:= by
  intro I
  induction I with
  | nil =>
    constructor
  | cons F I IH =>
    constructor
    . apply P.forces.weaken
      exact F
    . exact IH


theorem Instantiate.weaken_cons {P: Presheaf} {Δ: Context} {Γ A env}:
  Instantiate P Δ env Γ -> Instantiate P (A :: Δ) (env.up 0 1) Γ
:= by
  intro H
  replace H := weaken H (Δ' := [A])
  simp at H
  exact H


@[simp]
theorem Instantiate.self {Γ} {PNE PNF} [inst: NPair PNE PNF]:
  Instantiate PNF Γ (Env.vars Γ.length) Γ
:= by
  induction Γ with
  | nil =>
    simp [Env.vars]
    constructor
  | cons T TS IH =>
    apply Instantiate.cons
    . apply inst.completeness.right
      apply inst.var
    . apply Instantiate.weaken_cons
      exact IH


theorem Instantiate.length {P} {Δ Γ: Context} {env: Env}:
  Instantiate P Δ env Γ -> env.length = Γ.length
:= by
  intro H
  induction H with
  | nil =>
    simp
  | cons =>
    simp_all


theorem Instantiate.index {P} {Δ: Context} {Γ env} (I: Instantiate P Δ env Γ) (i: Nat):
  (h: i < Γ.length) ->
  P.forces Δ (env[i]'(by simp_all [I.length])) Γ[i]
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


class Presheaf.Typing (P: Presheaf) where
  typing {Γ t T}: P Γ t T -> Γ.Typing t T


def Presheaf.typing (P: Presheaf) [inst: P.Typing]:
  forall {Γ t T}, P Γ t T -> Γ.Typing t T
:= inst.typing


/--
One part needed for the well-definedness of the natural transformation.
-/
theorem Instantiate.typing {PNE PNF: Presheaf} [inst: NPair PNE PNF] [PNF.Typing] {Δ Γ: Context} {env t T}:
  Instantiate PNF Δ env Γ ->
  Γ.Typing t T ->
  Δ.Typing (t.msubst env) T
:= by
  intro I HT
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
    replace F := inst.completeness.left F
    apply Presheaf.Typing.typing F
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
    . apply inst.completeness.right
      apply inst.var
    . apply Instantiate.weaken_cons
      exact I


class Presheaf.MSubst (P: Presheaf) where
  msubst {Γ t T1 T2 Δ' Δ s env}:
    Context.Typing (T1 :: Γ) t T2 ->
    Instantiate P Δ env Γ ->
    P (Δ' ++ Δ) s T1 ->
    P.forces (Δ' ++ Δ) (Tm.msubst (s :: Env.up 0 (List.length Δ') env) t) T2 ->
    P.forces (Δ' ++ Δ) ((Tm.up 0 (List.length Δ') (Tm.msubst env t.abs)).app s) T2


/--
The natural transformation, i.e., the logical entailment.
Each `Γ` and `T` are two objects with a term a morphism between them.
If `Γ` and `T` are interpreted as presheaves `[Γ]` and `[T]`, then the morphism
`Γ ⊢ t: T` is interpreted as a natural transformation from `[Γ]` to `[T]`.
That is, for each `Δ` in the category `Context`, you have to find a function from `[Γ](Δ)` to `[T](Δ)`.
The former is some `Δ ⊩ env: Γ`, and the later is `Δ ⊩ t[env]: T`
-/
theorem NPair.soundness {PNE PNF: Presheaf} [inst: NPair PNE PNF] [PNF.MSubst] {Γ: Context} {t T}:
  Γ.Typing t T ->
  forall Δ env, Instantiate PNF Δ env Γ -> PNF.forces Δ (t.msubst env) T
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
    simp [Presheaf.forces, forcePred] at IH1
    replace IH1 := IH1 (Γ' := [])
    simp at IH1
    apply IH1
    exact IH2
  | abs HT IH =>
    rename_i Γ M T1 T2
    simp [Presheaf.forces, forcePred]
    intro s Δ' F
    have H := inst.completeness.left F
    have K: Instantiate PNF (Δ' ++ Δ) (s :: env.up 0 Δ'.length) (T1 :: Γ) := by
      apply Instantiate.cons
      . exact F
      . apply Instantiate.weaken
        exact I
    specialize IH _ _ K
    apply Presheaf.MSubst.msubst <;>
    . assumption
