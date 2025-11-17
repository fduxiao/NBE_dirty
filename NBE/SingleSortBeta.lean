import NBE.Rel
import NBE.Map

namespace SingleSortBeta


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


theorem Tm.subst_down {t s: Tm} {c i n: Nat}:
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
Then, `Typing` is preserved by substitution. This is the general lemma.
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
Then, `Typing` is preserved by substitution.
-/
theorem Context.subst_typing {Γ: Context} {A t v T}:
  Typing (A :: Γ) t T ->
  Typing Γ v A ->
  Typing Γ (t.subst 0 v.up0).down0 T
:= by
  apply Context.subst_typing_lemma (Γ2 := [])


/-!
### Equalities between Morphisms
-/


mutual
  inductive Tm.NE: Tm -> Prop where
    | var {x}: NE (.var x)
    | app {s t}: NE s -> NF t -> NE (s.app t)

  inductive Tm.NF: Tm -> Prop where
    | neutral {t}: NE t -> NF t
    | abs {t}: NF t -> NF t.abs
end


inductive Tm.step: Tm -> Tm -> Prop where
  -- beta reduction
  | appAbs {t s: Tm}: Tm.step (.app t.abs s) (t.subst 0 s.up0).down0
  -- congrunence relation
  | abs {t1 t2: Tm}: Tm.step t1 t2 -> Tm.step t1.abs t2.abs
  | app1 {t1 t2 s: Tm}: Tm.step t1 t2 -> Tm.step (.app t1 s) (.app t2 s)
  | app2 {t s1 s2: Tm}: Tm.step s1 s2 -> Tm.step (.app t s1) (.app t s2)



def Tm.mstep: Tm -> Tm -> Prop := RTCl Tm.step
def Tm.Eq := ECl Tm.step
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


theorem Tm.Eq.abs {t1 t2: Tm}:
  t1.Eq t2 -> t1.abs.Eq t2.abs
:= by
  apply ECl.keep_cong Tm.step.abs


theorem Tm.Eq.app1 {t1 t2 s: Tm}:
  t1.Eq t2 -> (t1.app s).Eq (t2.app s)
:= by
  apply ECl.keep_cong Tm.step.app1


theorem Tm.Eq.app2 {t s1 s2: Tm}:
  s1.Eq s2 -> (t.app s1).Eq (t.app s2)
:= by
  apply ECl.keep_cong Tm.step.app2


theorem Tm.NF.normal {t: Tm}:
  t.NF -> t.normal
:= by
  intro H
  intro ⟨t', S⟩
  induction t generalizing t' with
  | var x =>
    cases S
  | app t1 t2 IH1 IH2 =>
    cases H with | neutral H =>
    cases H with | app H1 H2 =>
    have H: t1.NF := by constructor; assumption
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


theorem Tm.normal.NF {t: Tm}:
  t.normal -> t.NF
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
      apply step.app1
      exact S
    replace IH1 := IH1 N1
    have N2: t2.normal := by
      intro ⟨y, S⟩
      apply H
      exists t1.app y
      apply step.app2
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
    apply NF.abs
    apply IH
    intro ⟨y, S⟩
    apply H
    constructor
    apply step.abs
    exact S


theorem Tm.step.typing {Γ: Context} {t t': Tm} {T}:
  t.step t' -> Γ.Typing t T -> Γ.Typing t' T
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



theorem Tm.N_up {t: Tm} {c n}:
  (t.NE <-> (t.up c n).NE) ∧ (t.NF <-> (t.up c n).NF)
:= by
  induction t generalizing c n with
  | var x =>
    grind [up, NE, NF]
  | app t1 t2 IH1 IH2 =>
    grind [up, NE, NF]
  | abs M IH =>
    grind [up, NE, NF]


theorem Tm.NE.up {t: Tm} {c n}:
  t.NE -> (t.up c n).NE
:= by
  apply Tm.N_up.left.mp


theorem Tm.NE.up_inv {t: Tm} {c n}:
  (t.up c n).NE -> t.NE
:= by
  apply Tm.N_up.left.mpr


theorem Tm.NF.up {t: Tm} {c n}:
  t.NF -> (t.up c n).NF
:= by
  apply Tm.N_up.right.mp


theorem Tm.NF.up_inv {t: Tm} {c n}:
  (t.up c n).NF -> t.NF
:= by
  apply Tm.N_up.right.mpr


theorem Tm.N_down {t: Tm} {c}:
  (t.NE <-> (t.down c).NE) ∧ (t.NF <-> (t.down c).NF)
:= by
  induction t generalizing c with
  | var x =>
    and_intros
    . grind [NF, NE, down]
    . grind [NF, NE, down]
  | app t1 t2 IH1 IH2 =>
    and_intros
    . grind [NF, NE, down]
    . grind [NF, NE, down]
  | abs M IH =>
    and_intros
    . grind [NF, NE, down]
    . grind [NF, NE, down]


theorem Tm.NE.down {t: Tm} {c}:
  t.NE -> (t.down c).NE
:= by
  apply Tm.N_down.left.mp


theorem Tm.NE.down_inv {t: Tm} {c}:
  (t.down c).NE -> t.NE
:= by
  apply Tm.N_down.left.mpr


theorem Tm.NF.down {t: Tm} {c}:
  t.NF -> (t.down c).NF
:= by
  apply Tm.N_down.right.mp


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
  | abs S IH=>
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


theorem Tm.Eq.up {c n} {t t': Tm}:
  t.Eq t' -> (t.up c n).Eq (t'.up c n)
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


theorem Tm.Eq.down {c} {t t': Tm}:
  t.Eq t' -> (t.down c).Eq (t'.down c)
:= by
  apply ECl.keep_cong Tm.step.down


theorem Tm.mstep.up_down {t t': Tm}:
  t.up0.mstep t' -> t.mstep t'.down0
:= by
  intro H
  replace H := Tm.mstep.down H (c := 0)
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
inductive Tm.step2: Tm -> Tm -> Prop where
  -- beta reduction
  | appAbs {t1 t2 s1 s2: Tm}: t1.step2 t2 -> s1.step2 s2 -> Tm.step2 (.app t1.abs s1) (t2.subst 0 s2.up0).down0
  -- congrunence relation
  | abs {t1 t2: Tm}: Tm.step2 t1 t2 -> Tm.step2 t1.abs t2.abs
  | app {t1 t2 s1 s2: Tm}: Tm.step2 t1 t2 -> Tm.step2 s1 s2 -> Tm.step2 (.app t1 s1) (.app t2 s2)
  -- refl
  | var {x: Nat}: Tm.step2 (.var x) (.var x)


theorem Tm.step2.refl {t: Tm}:
  t.step2 t
:= by
  induction t <;> grind [step2]


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
  | abs S IH =>
    apply mstep.abs
    exact IH
  | app S1 S2 IH1 IH2 =>
    apply mstep.app
    . apply IH1
    . apply IH2


theorem Tm.step2_eval {t: Tm}:
  t.step2 t.eval
:= by
  induction t with
  | var x =>
    simp [eval]
    apply step2.refl
  | abs t IH =>
    simp [eval]
    apply step2.abs
    apply IH
  | app t1 t2 IH1 IH2 =>
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
      simp [eval] at *
      apply step2.appAbs
      . generalize E: t1.eval.abs = t1' at IH1
        cases IH1 with
        | abs =>
          cases E
          assumption
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
        cases n with
        | zero =>
          simp [Subst.id, Tm.ssubst, Subst.step, Subst.comp, Subst.up]
        | succ =>
          simp [Subst.id, Tm.ssubst, Subst.step, Subst.comp, Subst.up]
      . simp [Tm.ssubst, Subst.step]


theorem Tm.step2.switch {t1 t2: Tm}:
  t1.step2 t2 ->
  t2.step2 t1.eval
:= by
  intro S
  induction S with
  | var =>
    apply Tm.step2_eval
  | abs S IH =>
    simp [eval]
    apply step2.abs
    apply IH
  | appAbs =>
    simp [eval]
    apply Tm.step2.down
    apply Tm.step2.subst
    . assumption
    . apply Tm.step2.up
      assumption
  | app S1 S2 IH1 IH2 =>
    rename_i t1 t2 s1 s2
    cases t1 with
    | var =>
      simp [eval] at *
      apply step2.app
      . exact IH1
      . exact IH2
    | app =>
      simp [eval] at *
      apply step2.app
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
          apply step2.appAbs
          . apply IH1
          . apply IH2


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


theorem Tm.eq_normal_mstep {t n: Tm}:
  t.Eq n -> n.normal -> t.mstep n
:= by
  intro S N
  obtain ⟨s, Hts, Hsn⟩ := Relation.church_rosser Tm.step S
  have E := N.MNormal Hsn
  cases E
  exact Hts



/-!
### Formalization of Contextual CCC
We first give some example of how to encode categories.
-/

structure CtxCCC.{u, v, w}: Sort ((max u v w ) + 1) where
  Context: Sort u
  Ty: Sort v
  i: Ty -> Context
  nil: Context
  cons: Ty -> Context -> Context
  morph: Context -> Ty -> Sort w


def TmCat: CtxCCC where
  Context := Context
  Ty := Ty
  i T := [T]
  nil := List.nil
  cons := List.cons
  morph Γ T := { t: Tm // Γ.Typing t T}


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


/-!
## Interpretation in Presheaf
Given a presheaf F, we can turn it into a functor from Tm to PSh(C).
F corresponds to the forcing relation with functoriality corresponding to monotonicity.
Semantic entailment in a Kripke structure is a natural transformation in the presheaf category.
The soundness is the functor from Tm to PSh(C)

We have to explain the following:
1. How to map `imp` given `Atom => F`
2. How to map a `Γ: Context` given its value on `Ty`
3. How to map a term `t` such that `Γ |- M: T` implies `[M]: [Γ] [T]` <- the natural transformation.
-/


/-!
### Normalization
We interpret it with presheaves.
-/

def Tm.forces (F: Tm -> Prop) (Γ: Context) (t: Tm) (T: Ty) :=
  match T with
  | .Atom =>
    Γ.Typing t T ∧ exists t', t.Eq t' ∧ F t'
  | .imp A B =>
    forall (s: Tm) Γ', forces F (Γ' ++ Γ) s A -> forces F (Γ' ++ Γ) ((t.up 0 Γ'.length).app s) B


theorem Tm.NF.forces_app {Γ' Γ t T}:
  forces NF Γ t T -> forces NF (Γ' ++ Γ) (t.up 0 Γ'.length) T
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
      . apply Tm.Eq.up
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


theorem Tm.NF.app1_inv {t s: Tm}:
  (t.app s).NF -> t.NF
:= by
  intro N
  cases N with | neutral N =>
  cases N with | app N =>
  apply NF.neutral
  exact N


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


theorem Tm.mstep_app_var_normal' {t s: Tm}:
  t.Eq t.down0.up0 ->
  (t.app (.var 0)).mstep s ->
  s.NF ->
  exists t', t.mstep t' ∧ t'.NF
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
      have I: t'.Eq t'.down0.up0 := by
        apply ECl.trans
        . apply ECl.reverse
          exact S'
        apply ECl.trans
        . apply I
        apply Tm.Eq.up
        apply Tm.Eq.down
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
      have S1: (M.abs.app (.var 0)).Eq s := by
        apply ECl.step
        . apply Tm.step.appAbs
        . apply RTCl.sub_ecl
          exact Hyz
      have S2: (M.abs.app (.var 0)).Eq (M.down 1) := by
        -- we first change the left to `M.abs.down0.up0`
        apply ECl.trans
        . apply Tm.Eq.app1
          exact I
        simp [Tm.down0, Tm.down]
        apply ECl.step
        . apply Tm.abs_up_app_step
        apply ECl.refl

      have S3: M.abs.down0.Eq s.abs := by
        simp [down0, down]
        apply Tm.Eq.abs
        apply ECl.trans
        . apply ECl.symm
          exact S2
        . exact S1

      rewrite [Tm.subst_up_down_var0] at Hyz
      exists s.abs.up0
      have N: s.abs.up0.NF := by
        apply NF.up
        apply NF.abs
        apply N
      and_intros
      . apply Tm.eq_normal_mstep _ N.normal
        apply ECl.trans
        . exact I
        apply Tm.Eq.up
        exact S3
      . exact N


theorem Tm.mstep_app_var_normal {t s: Tm}:
  ((t.up0.app (.var 0)).mstep s) -> s.NF -> exists t', t.Eq t' ∧ t'.NF
:= by
  intro S N
  have E: t.up0.Eq (t.up0.down0.up0) := by simp; apply ECl.refl
  obtain ⟨s, S, N⟩ := Tm.mstep_app_var_normal' E S N
  exists s.down0
  and_intros
  . apply RTCl.sub_ecl
    apply Tm.mstep.up_down
    exact S
  . apply N.down


theorem completeness {Γ T}:
  (forall {t}, Tm.forces Tm.NF Γ t T -> Γ.Typing t T ∧ exists t', t.Eq t' ∧ Tm.NF t') ∧
  (forall {t}, (Γ.Typing t T ∧ exists t', t.Eq t' ∧ Tm.NE t') -> Tm.forces Tm.NF Γ t T)
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
      apply Tm.NF.neutral
      assumption
  | imp A B IHA IHB =>
    and_intros
    . intro t HF
      simp [Tm.forces] at HF
      have H: Tm.forces Tm.NF ([A] ++ Γ) (.var 0) A := by
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
        have H := Tm.eq_normal_mstep S N.normal
        clear S IHA HF
        apply Tm.mstep_app_var_normal
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
          . apply Tm.Eq.app1
            apply Tm.Eq.up
            exact S
          . apply Tm.Eq.app2
            exact S'
        . apply Tm.NE.app
          . apply N.up
          . exact N'


abbrev Env := FinMap Tm

def Env.up (c n: Nat): Env -> Env
  | [] => []
  | x :: xs => (x.up c n) :: (up c n xs)


@[simp]
theorem Env.up_length_eq {e: Env} {c n}:
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
    Tm.forces Tm.NF Δ t T ->
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
    . apply Tm.NF.forces_app
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
  Tm.forces Tm.NF Δ (env[i]'(by simp_all [I.length])) Γ[i]
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


theorem Tm.step.forces {Γ} {t t': Tm} {T}:
  t.step t' ->
  forces NF Γ t T ->
  forces NF Γ t' T
:= by
  intro S F
  induction T generalizing Γ t t' with
  | Atom =>
    simp [Tm.forces] at *
    and_intros
    . apply Tm.step.typing
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
    . apply Tm.step.app1
      apply Tm.step.up
      exact S
    . apply F
      exact F'


theorem Tm.step.forces' {Γ: Context} {t t': Tm} {T}:
  Γ.Typing t T ->
  t.step t' ->
  Tm.forces NF Γ t' T ->
  Tm.forces NF Γ t T
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
    . apply Tm.step.app1
      apply Tm.step.up
      exact S
    . apply F
      exact F'


theorem Tm.mstep.forces' {Γ: Context} {t t': Tm} {T}:
  Γ.Typing t T ->
  t.mstep t' ->
  Tm.forces NF Γ t' T ->
  Tm.forces NF Γ t T
:= by
  intro HT S F
  induction S with
  | refl =>
    assumption
  | step Hxy Hyz IH =>
    apply Tm.step.forces' HT Hxy
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
  forall Δ env, Instantiate Δ env Γ -> Tm.forces Tm.NF Δ (t.msubst env) T
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
    apply Tm.mstep.forces' _ _ IH
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
      apply Tm.step.compute
      apply Tm.step.appAbs_ssubst
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
        -- again, we only have to prove the equality of the `Subst`
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
  Γ.Typing t T -> exists t', t.Eq t' ∧ t'.NF
:= by
  intro HT
  let entailment := soundness HT
  specialize entailment Γ (Env.vars Γ.length) Instantiate.self
  simp at entailment
  let F := completeness.left entailment
  apply F.right
