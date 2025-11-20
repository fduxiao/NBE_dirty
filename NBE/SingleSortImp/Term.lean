import NBE.Rel
import NBE.Map

namespace SingleSortImp


inductive Ty where
  | Atom: Ty
  | imp: Ty -> Ty -> Ty
  deriving Repr


/--
Terms using de Bruijn index
-/
inductive Tm where
  | var: Nat -> Tm
  | abs: Tm -> Tm
  | app: Tm -> Tm -> Tm
  deriving Repr, BEq


def Tm.up (c i: Nat): Tm -> Tm
  | .var n => .var $ if n < c then n else (n + i)
  | .abs M => .abs (M.up (c + 1) i)
  | .app M N => .app (M.up c i) (N.up c i)


def Tm.down (c: Nat): Tm -> Tm
  | .var n => .var $ if n <= c then n else (n - 1)  -- after the down, the variable should be larger than c
  | .abs M => .abs (M.down (c + 1))
  | .app M N => .app (M.down c) (N.down c)


def Tm.size: Tm -> Nat
  | .var _ => 0
  | .app t1 t2 => t1.size + t2.size + 1
  | .abs t => t.size + 1


@[simp]
theorem Tm.up_size {t: Tm} {c n: Nat}:
  (t.up c n).size = t.size
:= by
  induction t generalizing c <;> grind [up, size]


@[simp]
theorem Tm.down_size {t: Tm} {c: Nat}:
  (t.down c).size = t.size
:= by
  induction t generalizing c <;> grind [down, size]


def Tm.strong_ind.{u} {motive: Tm -> Sort u}
  (var: forall x, motive (.var x))
  (abs: forall M: Tm, (forall t: Tm, t.size < M.abs.size -> motive t) -> motive M.abs)
  (app: forall t1 t2: Tm, (forall t: Tm, t.size < (t1.app t2).size -> motive t) -> motive (t1.app t2))
  (t: Tm)
:
  motive t
:=
  match t with
  | .var x => var x
  | .abs M => abs M (fun t _ => strong_ind var abs app t)
  | .app t1 t2 => app t1 t2 (fun t _ => strong_ind var abs app t)
termination_by t.size
decreasing_by
  . trivial
  . trivial


@[simp]
theorem Tm.up_0 {t: Tm} {c}:
  t.up c 0 = t
:= by
  induction t generalizing c <;>
    simp [up] <;>
    solve_by_elim


theorem Tm.shift_up_add {t: Tm} {c} {n m}:
  (t.up c n).up c m = t.up c (n + m)
:= by
  induction t generalizing c with
  | var x =>
    simp [up]
    split
    next H =>
      simp
    next H =>
      have H: ¬ x + n < c := by
        omega
      simp [H]
      omega
  | app =>
    simp [up]
    solve_by_elim
  | abs M IH =>
    simp [up]
    apply IH


theorem Tm.up_switch_lemma {t: Tm} {c c' n n': Nat}:
  (t.up (c + c') n).up c' n' = (t.up c' n').up (c + c' + n') n
:= by
  induction t generalizing c c' with
  | var x =>
    simp [up]
    split
    . grind
    . grind
  | app =>
    simp [up]
    solve_by_elim
  | abs M IH =>
    simp [up]
    have E1: c + c' + 1 = c + (c' + 1) := by omega
    have E2: c + c' + n' + 1 = c + (c' + 1) + n' := by omega
    rewrite [E1, E2]
    apply IH


theorem Tm.is_var0_or_not {t: Tm}:
  t = (.var 0) ∨ t ≠ (.var 0)
:= by
  cases t with
  | var x =>
    cases x with
    | zero =>
      left
      eq_refl
    | _ =>
      right
      intro H
      cases H
  | _ =>
    right
    intro H
    cases H


def Tm.up0 := Tm.up 0 1

@[simp]
theorem Tm.up0_size {t: Tm}:
  t.up0.size = t.size
:= by
  simp [up0]


@[simp]
theorem Tm.var_up {n: Nat}:
  (Tm.var n).up0 = (Tm.var $ n + 1)
:= by
  simp [up0, up]


@[simp]
theorem Tm.app_up {M1 M2: Tm}:
  (M1.app M2).up0 = (M1.up0.app M2.up0)
:= by
  simp [up0, up]


theorem Tm.up0_switch {t: Tm} {c n: Nat}:
  (t.up c n).up0 = t.up0.up (c + 1) n
:= by
  unfold Tm.up0
  apply Tm.up_switch_lemma (c' := 0) (n' := 1)


def Tm.down0: Tm -> Tm := Tm.down 0


@[simp]
theorem Tm.down0_size {t: Tm}:
  t.down0.size = t.size
:= by
  simp [down0]


@[simp]
theorem Tm.var_down {n: Nat}:
  (Tm.var n).down0 = (Tm.var $ n - 1)
:= by
  simp [down0, down]
  omega


@[simp]
theorem Tm.app_down {M1 M2: Tm}:
  (M1.app M2).down0 = (M1.down0.app M2.down0)
:= by
  simp [down0, down]


@[simp]
theorem Tm.up_down_eq {c} {t: Tm}:
  (t.up c 1).down c = t
:= by
  induction t generalizing c with
  | var x =>
    simp [up, down]
    split
    next H =>
      grind
    next H =>
      grind
  | app t1 t2 IH1 IH2 =>
    simp at *
    simp [up, down]
    simp_all
  | abs M IH =>
    simp at *
    simp [up, down]
    apply IH


@[simp]
theorem Tm.up_down_eq0 (t: Tm):
  t.up0.down0 = t
:= by
  simp [up0, down0]


def Tm.subst (t: Tm) (x: Nat) (s: Tm): Tm :=
  match t with
  | .var y => if y = x then s else .var y
  | .abs M => .abs $ M.subst (x + 1) s.up0
  | .app M N => .app (M.subst x s) (N.subst x s)


theorem Tm.subst_up {t s: Tm} {c i n: Nat}:
  (t.up (c + i + 1) n).subst i (s.up (c + i + 1) n) = (t.subst i s).up (c + i + 1) n
:= by
  induction t generalizing c i n s with
  | var x =>
    simp [up, subst]
    grind [up]
  | app t1 t2 IH1 IH2 =>
    simp [up, subst]
    grind
  | abs t IH =>
    simp [up, subst] at *
    rewrite [Tm.up0_switch]
    have E: c + i + 1 + 1 = c + (i + 1) + 1 := by ac_nf
    rewrite [E]
    apply IH


theorem Tm.subst_up_var0 {t s: Tm} {c n: Nat}:
  (t.up (c + 1) n).subst 0 (s.up (c + 1) n) = (t.subst 0 s).up (c + 1) n
:= by
  apply subst_up (i := 0)


@[simp]
theorem Tm.subst_up_down_var {t: Tm} {i: Nat}:
  (t.subst i (var $ i + 1)).down i = t.down i
:= by
  induction t generalizing i with
  | var x =>
    simp [subst]
    split
    . simp [down]
      simp_all
    . simp [down]
  | app t1 t2 IH1 IH2 =>
    simp [subst, down]
    and_intros
    . apply IH1
    . apply IH2
  | abs M IH =>
    simp [subst, down]
    apply IH


@[simp]
theorem Tm.subst_up_down_var0 {t: Tm}:
  (t.subst 0 (var 0).up0).down0 = t.down0
:= by
  simp [up0, down0]
  apply Tm.subst_up_down_var


def Rename := Nat -> Nat
def Rename.abs (a: Rename): Rename
  | 0 => 0
  | n + 1 => a n + 1


def Tm.rename (a: Rename): Tm -> Tm
  | .var x => .var (a x)
  | .app t1 t2 => .app (t1.rename a) (t2.rename a)
  | .abs t => .abs (t.rename a.abs)


def Rename.up (c i: Nat): Rename
  | n => if n < c then n else n + i


@[simp]
theorem Rename.up_abs {c i: Nat}:
  (Rename.up c i).abs = Rename.up (c + 1) i
:= by
  funext n
  induction n with
  | zero =>
    simp [up, abs]
  | succ m IH =>
    grind [up, abs]


theorem Tm.up_rename {t: Tm} {c i}:
  t.up c i = t.rename (Rename.up c i)
:= by
  induction t generalizing c i with
  | var x =>
    simp [up, rename, Rename.up]
  | app t1 t2 IH1 IH2 =>
    simp [up, rename]
    solve_by_elim
  | abs t IH =>
    simp [up, rename]
    apply IH


def Rename.down (c: Nat): Rename
  | n => if n <= c then n else n - 1


@[simp]
theorem Rename.down_abs {c: Nat}:
  (Rename.down c).abs = Rename.down (c + 1)
:= by
  funext n
  induction n with
  | zero =>
    simp [down, abs]
  | succ m IH =>
    grind [down, abs]


theorem Tm.down_rename {t: Tm} {c}:
  t.down c = t.rename (Rename.down c)
:= by
  induction t generalizing c with
  | var x =>
    simp [down, rename, Rename.down]
  | app t1 t2 IH1 IH2 =>
    simp [down, rename]
    solve_by_elim
  | abs t IH =>
    simp [down, rename]
    apply IH


@[simp]
theorem Rename.abs_comp {a1 a2: Rename}:
  Rename.abs (a2 ∘ a1) = a2.abs ∘ a1.abs
:= by
  funext n
  induction n with
  | zero =>
    simp [abs]
  | succ =>
    grind [abs]


@[simp]
theorem Tm.rename_twice {t: Tm} {a1 a2: Rename}:
  (t.rename a1).rename a2 = t.rename (a2 ∘ a1)
:= by
  induction t generalizing a1 a2 with
  | var x =>
    simp [rename]
  | app =>
    grind [rename]
  | abs t IH =>
    simp [rename]
    rewrite [IH]
    simp


def Subst := Nat -> Tm
def Subst.abs (s: Subst): Subst
  | 0 => (.var 0)
  | n + 1 => (s n).up0


def Tm.ssubst (s: Subst): Tm -> Tm
  | var x => s x
  | app t1 t2 => app (t1.ssubst s) (t2.ssubst s)
  | abs M => abs (M.ssubst s.abs)


def Subst.id: Subst := fun n => .var n


@[simp]
theorem Subst.id_abs:
  Subst.id.abs = Subst.id
:= by
  funext n
  induction n with
  | zero =>
    simp [Subst.id, Subst.abs]
  | _ =>
    simp [Subst.id, Subst.abs]


theorem Tm.ssubst_id (t: Tm):
  t = t.ssubst Subst.id
:= by
  induction t with
  | var x =>
    simp [ssubst, Subst.id]
  | app =>
    simp [ssubst]
    solve_by_elim
  | abs M IH =>
    simp [ssubst]
    apply IH


def Subst.term (i: Nat) (s: Tm): Subst
  | n => if n = i then s else (.var n)


@[simp]
theorem Subst.term_abs {i: Nat} {s: Tm}:
  (Subst.term i s).abs = (Subst.term (i + 1) s.up0)
:= by
  funext n
  induction n with
  | zero =>
    simp [abs, term]
  | succ m IH =>
    simp [abs, term]
    simp [Tm.up0]
    split
    . eq_refl
    . simp [Tm.up]


theorem Tm.subst_ssubst {t s: Tm} {i: Nat}:
  t.subst i s = t.ssubst (.term i s)
:= by
  induction t generalizing i s with
  | var x =>
    simp [subst, ssubst, Subst.term]
  | app t1 t2 IH1 IH2 =>
    simp [subst, ssubst]
    solve_by_elim
  | abs t IH =>
    simp [subst, ssubst]
    rewrite [IH]
    eq_refl


def Subst.rename (s: Subst) (a: Rename): Subst
  | n => (s n).rename a


@[simp]
theorem Rename.switch {a: Rename}:
  (a.abs ∘ Rename.up 0 1) = Rename.up 0 1 ∘ a
:= by
  funext n
  cases n <;> simp [abs, up]


@[simp]
theorem Subst.rename_abs {s: Subst} {a: Rename}:
  (s.abs.rename a.abs) = (s.rename a).abs
:= by
  funext n
  induction n with
  | zero =>
    simp [abs, rename, Tm.rename, Rename.abs]
  | succ m IH =>
    simp [abs, rename, Tm.up0]
    repeat rewrite [Tm.up_rename]
    simp


@[simp]
theorem Tm.ssubst_rename {a: Rename} {s: Subst} {t: Tm}:
  (t.ssubst s).rename a = t.ssubst (s.rename a)
:= by
  induction t generalizing a s with
  | var x =>
    simp [Tm.ssubst, Subst.rename]
  | app t1 t2 IH1 IH2 =>
    simp [Tm.ssubst, rename]
    solve_by_elim
  | abs t IH =>
    simp [Tm.ssubst, rename]
    rewrite [IH]
    simp


def Subst.step (s: Tm): Subst
  | 0 => s
  | n + 1 => .var n


theorem Tm.step_ssubst {t s: Tm}:
  (t.subst 0 s.up0).down0 = t.ssubst (.step s)
:= by
  unfold down0
  simp [Tm.subst_ssubst, Tm.down_rename]
  congr
  funext n
  simp [Subst.rename]
  simp [Subst.term]
  split
  next E => -- n = 0
    simp [Subst.step]
    simp [E]
    rewrite [<-Tm.down_rename]
    unfold up0
    simp
  next NE =>  -- n ≠ 0
    simp [rename, Subst.step]
    simp [Rename.down]
    grind


def Rename.subst (a: Rename) (s: Subst): Subst
  | n => s (a n)


@[simp]
theorem Tm.rename_ssubst {a: Rename} {s: Subst} {t: Tm}:
  (t.rename a).ssubst s = t.ssubst (a.subst s)
:= by
  induction t generalizing a s with
  | var x =>
    simp [rename, ssubst, Rename.subst]
  | app =>
    simp [rename, ssubst]
    solve_by_elim
  | abs M IH =>
    simp [rename, ssubst]
    rewrite [IH]
    congr
    funext n
    induction n with
    | zero =>
      simp [Rename.subst, Rename.abs, Subst.abs]
    | _ =>
      simp [Rename.subst, Rename.abs, Subst.abs]


def Subst.comp (s2 s1: Subst): Subst
  | n => (s1 n).ssubst s2


@[simp]
theorem Subst.comp_abs {s1 s2: Subst}:
  (s2.abs.comp s1.abs) = (s2.comp s1).abs
:= by
  funext n
  induction n with
  | zero =>
    simp [abs, comp, Tm.ssubst]
  | succ m IH =>
    simp [abs, comp]
    unfold Tm.up0
    simp [Tm.up_rename]
    congr
    funext k
    cases k with
    | zero =>
      simp [Rename.subst, Rename.up, Subst.abs, Subst.rename]
      unfold Tm.up0
      simp [Tm.up_rename]
    | succ =>
      simp [Rename.subst, Rename.up, Subst.abs, Subst.rename]
      unfold Tm.up0
      simp [Tm.up_rename]


@[simp]
theorem Tm.ssubst_twice {t: Tm} {s1 s2: Subst}:
  (t.ssubst s1).ssubst s2 = t.ssubst (s2.comp s1)
:= by
  induction t generalizing s1 s2 with
  | var x =>
    simp [ssubst, Subst.comp]
  | app t1 t2 IH1 IH2 =>
    simp [ssubst]
    solve_by_elim
  | abs M IH =>
    simp [ssubst]
    rewrite [IH]
    simp


@[simp]
theorem Tm.ssubst_comp_assoc {s1 s2 s3: Subst}:
  (s1.comp (s2.comp s3)) = (s1.comp s2).comp s3
:= by
  funext n
  simp [Subst.comp]


def Subst.up (c i: Nat): Subst
  | n => .var $ if n < c then n else n + i


@[simp]
theorem Subst.up_abs {c i: Nat}:
  (Subst.up c i).abs = Subst.up (c + 1) i
:= by
  funext n
  induction n with
  | zero =>
    simp [up, abs]
  | succ m IH =>
    simp [abs, up]
    grind


theorem Tm.up_ssubst {t: Tm} {c i}:
  t.up c i = t.ssubst (Subst.up c i)
:= by
  induction t generalizing c i with
  | var x =>
    simp [up, ssubst, Subst.up]
  | app t1 t2 IH1 IH2 =>
    simp [up, ssubst]
    solve_by_elim
  | abs t IH =>
    simp [up, ssubst]
    apply IH


def Subst.down (c: Nat): Subst
  | n => .var $ if n <= c then n else n - 1


@[simp]
theorem Subst.down_abs {c: Nat}:
  (Subst.down c).abs = Subst.down (c + 1)
:= by
  funext n
  induction n with
  | zero =>
    simp [down, abs]
  | succ m IH =>
    simp [abs, down]
    grind


theorem Tm.down_ssubst {t: Tm} {c}:
  t.down c = t.ssubst (Subst.down c)
:= by
  induction t generalizing c with
  | var x =>
    simp [down, ssubst, Subst.down]
  | app t1 t2 IH1 IH2 =>
    simp [down, ssubst]
    solve_by_elim
  | abs t IH =>
    simp [down, ssubst]
    apply IH


@[simp]
theorem Tm.ssubst_step_up0_eq {s t: Tm}:
  Tm.ssubst (Subst.step s) t.up0 = t
:= by
  unfold Tm.up0
  rewrite [Tm.up_ssubst]
  rewrite [Tm.ssubst_id t]
  simp_all
  congr


/--
This shows the `funext` following `congr` is constructive.
-/
theorem Tm.ssubst_congr {s1 s2: Subst} {t: Tm}:
  (forall n, s1 n = s2 n) ->
  t.ssubst s1 = t.ssubst s2
:= by
  intro H
  induction t generalizing s1 s2 with
  | var x =>
    simp [ssubst]
    apply H
  | app t1 t2 =>
    simp [ssubst]
    solve_by_elim
  | abs t IH =>
    simp [ssubst]
    apply IH
    intro n
    cases n with
    | zero =>
      simp [Subst.abs]
    | succ =>
      simp [Subst.abs]
      rewrite [H]
      eq_refl


def Tm.bound: Tm -> Nat
  | .var x => x + 1
  | .app t1 t2 => max t1.bound t2.bound
  | .abs M => M.bound - 1


/--
You only have to check the equality until `Tm.bound`.
-/
theorem Tm.ssubst_congr_lt {s1 s2: Subst} {t: Tm}:
  (forall n, n < t.bound -> s1 n = s2 n) ->
  t.ssubst s1 = t.ssubst s2
:= by
  intro H
  induction t generalizing s1 s2 with
  | var =>
    simp [Tm.bound] at H
    simp [ssubst]
    apply H
    omega
  | app =>
    simp [Tm.bound] at H
    simp [ssubst]
    grind
  | abs M IH =>
    simp [Tm.bound] at H
    simp [ssubst]
    apply IH
    intro n I
    simp [Subst.abs]
    split
    . eq_refl
    . congr
      apply H
      omega


/-!
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

This is the free Contextual CCC Tm. If we have another contextual (C, T) and some c ∈ C,
we can generate the interpretation from Tm to C.
-/
abbrev Context := FinMap Ty


/--
Typing relation shows the moprhisms between objects.
-/
inductive Context.Typing: Context -> Tm -> Ty -> Prop where
  | var {Γ: Context} {x: Nat} {T: Ty}:
    Γ.lookup x = some T ->
    Typing Γ (.var x) T
  | abs {Γ: Context} {M: Tm} {T1 T2: Ty}:
    Typing (T1 :: Γ) M T2 ->
    Typing Γ (.abs M) (T1.imp T2)
  | app {Γ: Context} {M N: Tm} {T1 T2: Ty}:
    Typing Γ M (T1.imp T2) ->
    Typing Γ N T1 ->
    Typing Γ (.app M N) T2


theorem Context.Typing.bound {Γ: Context} {t T}:
  Γ.Typing t T -> t.bound ≤ Γ.length
:= by
  intro H
  induction H with
  | var H =>
    simp [Tm.bound]
    replace H := FinMap.lookup_some_lt H
    omega
  | app =>
    simp [Tm.bound]
    omega
  | abs H IH =>
    simp [Tm.bound] at *
    exact IH


/-!
## The Category of Weakenings
Then we start to make the interpretation in the presheaf category
`Δ` is Stronger then `Γ` iff it is obtained by insertion.
This is too strong. We only need it to be a prefix relation.
-/


/--
The original definition.
-/
inductive Context.Stronger: Context -> Context -> Type where
  | nil: Context.Stronger [] []
  | cons {Γ Δ: Context} {A: Ty}: Γ.Stronger Δ -> Context.Stronger (A :: Γ) Δ
  | cons2 {Γ Δ: Context} {A: Ty}: Γ.Stronger Δ -> Context.Stronger (A :: Γ) (A :: Δ)


def Context.Stronger.comp {Γ Δ Ξ: Context}:
  (Δ.Stronger Ξ) -> (Γ.Stronger Δ) -> (Γ.Stronger Ξ)
  | w', .nil => w'
  | w', .cons w => .cons $ w'.comp w
  | .cons w', .cons2 w => .cons $ w'.comp w
  | .cons2 w', .cons2 w => .cons2 $ w'.comp w


theorem Context.weaken_lemma {Γ1 Γ2 Γ3: Context} {M: Tm} {T}:
  Context.Typing (Γ1 ++ Γ2) M T ->
  Context.Typing (Γ1 ++ (Γ3 ++ Γ2)) (M.up Γ1.length Γ3.length) T
:= by
  intro HT
  induction M generalizing Γ1 Γ2 Γ3 T with
  | var x =>
    cases HT with | var HT =>
    simp [Tm.up]
    split
    next H =>
      constructor
      simp_all [FinMap.lookup_left H]
    next H =>
      constructor
      grind [FinMap.lookup_right]
  | abs M IH =>
    cases HT with | abs HT =>
    rename_i T1 T2
    simp [Tm.up]
    constructor
    conv =>
      pattern T1 :: (Γ1 ++ (Γ3 ++ Γ2))
      change (T1 :: Γ1) ++ (Γ3 ++ Γ2)
    apply IH
    simp_all
  | app M1 M2 IH1 IH2 =>
    cases HT with | app H1 H2 =>
    simp [Tm.up]
    constructor
    . apply IH1
      exact H1
    . apply IH2
      exact H2


theorem Context.weaken_inv_lemma {Γ1 Γ2 Γ3: Context} {M: Tm} {T}:
  Context.Typing (Γ1 ++ (Γ3 ++ Γ2)) (M.up Γ1.length Γ3.length) T ->
  Context.Typing (Γ1 ++ Γ2) M T
:= by
  intro HT
  induction M generalizing Γ1 Γ2 Γ3 T with
  | var x =>
    simp [Tm.up] at HT
    split at HT
    next H =>
      cases HT with | var HT =>
      constructor
      simp_all [FinMap.lookup_left H]
    next H =>
      cases HT
      constructor
      grind [FinMap.lookup_right]
  | abs M IH =>
    simp [Tm.up] at HT
    cases HT with | abs HT =>
    rename_i T1 T2
    constructor
    conv at HT =>
      pattern T1 :: (Γ1 ++ (Γ3 ++ Γ2))
      change (T1 :: Γ1) ++ (Γ3 ++ Γ2)
    specialize IH HT
    simp at IH
    apply IH
  | app M1 M2 IH1 IH2 =>
    simp [Tm.up] at HT
    cases HT with | app H1 H2 =>
    constructor
    . apply IH1
      exact H1
    . apply IH2
      exact H2


theorem Context.weaken_cons {Γ: Context} {t: Tm} {T T'}:
  Γ.Typing t T ->
  Context.Typing (T' :: Γ) t.up0 T
:= by
  intro HT
  conv =>
    fun
    fun
    arg 1
    change [] ++ ([T'] ++ Γ)
  apply weaken_lemma
  simp_all


theorem Context.weaken_cons_inv {Γ: Context} {t: Tm} {T T'}:
  Context.Typing (T' :: Γ) t.up0 T ->
  Γ.Typing t T
:= by
  intro HT
  conv at HT =>
    fun
    fun
    arg 1
    change [] ++ ([T'] ++ Γ)
  unfold Tm.up0 at HT
  replace HT := weaken_inv_lemma HT
  simp at HT
  exact HT


theorem Context.weaken_app {Γ1 Γ2: Context} {M: Tm} {T}:
  Context.Typing Γ1 M T ->
  Context.Typing (Γ2 ++ Γ1) (M.up 0 Γ2.length) T
:= by
  intro H
  conv at H =>
    arg 1
    change [] ++ Γ1
  conv =>
    pattern (Γ2 ++ Γ1)
    change [] ++ (Γ2 ++ Γ1)
  apply Context.weaken_lemma
  exact H


theorem Context.weaken_app_inv {Γ1 Γ2: Context} {M: Tm} {T}:
  Context.Typing (Γ2 ++ Γ1) (M.up 0 Γ2.length) T ->
  Context.Typing Γ1 M T
:= by
  intro H
  conv at H =>
    arg 1
    change [] ++ (Γ2 ++ Γ1)
  conv =>
    arg 1
    change [] ++ Γ1
  apply Context.weaken_inv_lemma
  exact H


/--
`Typing` is preserved by substitution. This is the general lemma.
-/
theorem Context.subst_typing_lemma {Γ1 Γ2: Context} {A t v T}:
  Typing (Γ2 ++ (A :: Γ1)) t T ->
  Typing (Γ2 ++ Γ1) v A ->
  Typing (Γ2 ++ Γ1) ((t.subst Γ2.length (v.up Γ2.length 1)).down Γ2.length) T
:= by
  intro H Hv
  induction t generalizing Γ1 Γ2 T v with
  | var x =>
    simp [Tm.subst]
    cases H with | var H =>
    have K: x < Γ2.length ∨ x = Γ2.length ∨ x > Γ2.length := by
      omega
    rcases K with K | K | K
    . have NE: ¬ (x = Γ2.length) := by omega
      simp [NE]; clear NE
      constructor
      have P: x ≤ Γ2.length := by omega
      simp [P]; clear P
      simp [FinMap.lookup_left K] at *
      exact H
    . simp_all
    . have NE: ¬ (x = Γ2.length) := by omega
      simp [NE]; clear NE
      constructor
      have L: ¬ x ≤ Γ2.length := by omega
      simp [L]; clear L
      have L: x - 1 ≥ Γ2.length := by omega
      simp [FinMap.lookup_right L]; clear L
      have L: x ≥ Γ2.length := by omega
      simp [FinMap.lookup_right L] at H ; clear L
      have E: x - Γ2.length = (x - 1 - Γ2.length) + 1 := by omega
      rewrite [E] at H
      simp at *
      exact H
  | app t1 t2 IH1 IH2 =>
    cases H with | app H1 H2 =>
    specialize IH1 H1 Hv
    specialize IH2 H2 Hv
    simp [Tm.subst]
    constructor
    . exact IH1
    . exact IH2
  | abs t IH =>
    cases H with | abs H =>
    rename_i T1 T2
    simp [Tm.subst, Tm.up0_switch]
    constructor
    specialize IH (Γ1 := Γ1) (Γ2 := T1 :: Γ2) (v := v.up0) H
    apply IH
    apply Context.weaken_cons
    exact Hv


/--
`Typing` is preserved by substitution.
-/
theorem Context.subst_typing {Γ: Context} {A t v T}:
  Typing (A :: Γ) t T ->
  Typing Γ v A ->
  Typing Γ (t.subst 0 v.up0).down0 T
:= by
  apply Context.subst_typing_lemma (Γ2 := [])
