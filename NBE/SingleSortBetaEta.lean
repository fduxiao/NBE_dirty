import NBE.Rel
import NBE.Map

namespace SingleSortBetaEta


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


inductive Tm.step: Tm -> Tm -> Prop where
  -- beta reduction
  | appAbs {t s: Tm}: Tm.step (.app t.abs s) (t.subst 0 s.up0).down0
  -- eta reduction
  | eta {t: Tm}: Tm.step (t.up0.app $ .var 0).abs t
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
  inductive NE: Context -> Tm -> Ty -> Prop where
    | var {Γ: Context} {x} {T}: Γ.lookup x = some T -> NE Γ (.var x) T
    | app {Γ} {t s} {T1 T2}: NE Γ t (T1.imp T2) -> NF Γ s T1 -> NE Γ (t.app s) T2

  inductive NF: Context -> Tm -> Ty -> Prop where
    | atom {Γ} {t}: NE Γ t .Atom -> NF Γ t .Atom
    | abs {Γ} {t} {T1 T2}: NF (T1 :: Γ) t T2 -> NF Γ t.abs (T1.imp T2)
end


theorem NFNE.typing {Γ: Context} {t T}:
  (NF Γ t T -> Γ.Typing t T) ∧ (NE Γ t T -> Γ.Typing t T)
:= by
  induction t generalizing Γ T with
  | _ =>
    grind [NF, NE, Context.Typing]


theorem NF.typing {Γ: Context} {t T}:
  NF Γ t T -> Γ.Typing t T
:= by
  apply NFNE.typing.left

theorem NE.typing {Γ: Context} {t T}:
  NE Γ t T -> Γ.Typing t T
:= by
  apply NFNE.typing.right


theorem Tm.N_weakening {Γ2 Γ3 Γ1 T} {t: Tm}:
  (NE (Γ2 ++ Γ1) t T <-> NE (Γ2 ++ (Γ3 ++ Γ1)) (t.up Γ2.length Γ3.length) T) ∧
  (NF (Γ2 ++ Γ1) t T <-> NF (Γ2 ++ (Γ3 ++ Γ1)) (t.up Γ2.length Γ3.length) T)
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
          grind [NE, NF]
      . intro N
        cases N with
        | atom N => cases N
        | abs N =>
          constructor
          grind [NE, NF]


theorem NE.weaken_app {Γ' Γ T} {t: Tm}:
  NE Γ t T -> NE (Γ' ++ Γ) (t.up 0 Γ'.length) T
:= by
  let H := (Tm.N_weakening (Γ2 := []) (Γ3 := Γ') (Γ1 := Γ) (t := t) (T := T))
  simp at H
  apply H.left.mp


theorem NF.weaken_app {Γ' Γ T} {t: Tm}:
  NF Γ t T -> NF (Γ' ++ Γ) (t.up 0 Γ'.length) T
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
  t.Eq t' -> (t.up c n).Eq (t'.up c n)
:= by
  intro S
  apply ECl.keep_cong Tm.step.up
  exact S


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

def Tm.forces (F: Context -> Tm -> Ty -> Prop) (Γ: Context) (t: Tm) (T: Ty) :=
  match T with
  | .Atom =>
    Γ.Typing t T ∧ exists t', t.Eq t' ∧ F Γ t' T
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
      . apply N.weaken_app
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


theorem completeness {Γ T}:
  (forall {t}, Tm.forces NF Γ t T -> Γ.Typing t T ∧ exists t', t.Eq t' ∧ NF Γ t' T) ∧
  (forall {t}, (Γ.Typing t T ∧ exists t', t.Eq t' ∧ NE Γ t' T) -> Tm.forces NF Γ t T)
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
      apply NF.atom
      assumption
  | imp A B IHA IHB =>
    and_intros
    . intro t HF
      simp [Tm.forces] at HF
      have H: Tm.forces NF ([A] ++ Γ) (.var 0) A := by
        apply IHA.right
        and_intros
        . constructor
          simp_all
        . exists (.var 0)
          and_intros
          . apply ECl.refl
          . constructor
            simp
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
      . exists t'.abs
        and_intros
        . have E: ((Tm.up 0 1 t).app (Tm.var 0)).abs.Eq t := by
            apply ECl.inclusion
            apply Tm.step.eta
          apply ECl.trans
          . symm
            exact E
          . apply Tm.Eq.abs
            exact S
        . constructor
          exact N
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
        . apply NE.app
          . apply N.weaken_app
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
    Tm.forces NF Δ t T ->
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
          simp
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
  Tm.forces NF Δ (env[i]'(by simp_all [I.length])) Γ[i]
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
          simp
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
  forall Δ env, Instantiate Δ env Γ -> Tm.forces NF Δ (t.msubst env) T
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
theorem Tm.NF_halts {Γ: Context} {t T}:
  Γ.Typing t T -> exists t', t.Eq t' ∧ NF Γ t' T
:= by
  intro HT
  let entailment := soundness HT
  specialize entailment Γ (Env.vars Γ.length) Instantiate.self
  simp at entailment
  let F := completeness.left entailment
  apply F.right




mutual
  inductive Tm.BNE: Tm -> Prop where
  | var {x}: Tm.BNE (.var x)
  | app {t1 t2}: Tm.BNE t1 -> Tm.BNF t2 -> Tm.BNE (t1.app t2)

  inductive Tm.BNF: Tm -> Prop where
  | neutral {t}: Tm.BNE t -> Tm.BNF t
  | abs {t}: Tm.BNF t -> Tm.BNF t.abs
end


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
  (NE Γ t T -> t.BNE) ∧ (NF Γ t T -> t.BNF)
:= by
  induction t generalizing Γ T with
  | _ =>
    grind [NE, NF, BNE, BNF]


theorem NE.BNE {Γ t T}:
  NE Γ t T -> t.BNE
:= by
  apply Tm.N_to_BN.left


theorem NF.BNF {Γ t T}:
  NF Γ t T -> t.BNF
:= by
  apply Tm.N_to_BN.right


theorem Tm.normalizing {Γ} {t: Tm} {T}:
  NF Γ t T -> exists n: Tm, t.mstep n ∧ n.normal
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
theorem Tm.up0_size {t: Tm}:
  t.up0.size = t.size
:= by
  simp [up0]


@[simp]
theorem Tm.down_size {t: Tm} {c: Nat}:
  (t.down c).size = t.size
:= by
  induction t generalizing c <;> grind [down, size]


@[simp]
theorem Tm.down0_size {t: Tm}:
  t.down0.size = t.size
:= by
  simp [down0]


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
  all_goals (try grind [size])
  simp [size]
  omega


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
        simp [size]
      . simp_all
        obtain ⟨s, E⟩ := Tm.not_free_up0 (by assumption)
        simp_all
        apply step2.eta
        apply IH
        simp [size]
        omega
    next E => -- otherwise
      specialize IH t (by grind [size])
      simp_all
      apply IH.abs
  | app t1 t2 IH =>
    have IH1 := IH t1 (by grind [size])
    have IH2 := IH t2 (by grind [size])
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
        grind [size]
      . apply IH
        grind [size]



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
      have IH1 := IH t1 (by grind [size]) S1
      have IH2 := IH t2 (by grind [size]) S2
      unfold eval
      split <;> try contradiction
      next E => -- β-redex
        simp_all; clear E
        rename_i t1 t2
        cases S1 with
        | abs S1 =>
          rename_i s1
          replace IH1 := IH t1 (by grind [size]) S1
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
            . grind [size]
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
      have IH1 := IH t1 (by grind [size]) S1
      have IH2 := IH t2 (by grind [size]) S2
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
      . simp [size]
        omega
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
          . grind [size]
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
            . simp [size]
              omega
            . replace S1 := S1.down (c := 0)
              simp [up0] at S1
              exact S1
          | appAbs S1 S2 =>
            rename_i t s _
            cases S2
            apply IH _ (by simp [size])
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
        . grind [size]
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


theorem Tm.Eq.normal_same {t1 t2: Tm}:
  t1.Eq t2 -> t1.normal -> t2.normal -> t1 = t2
:= by
  intro E N1 N2
  obtain ⟨s, H1s, H2s⟩ := ChurchRosser.church_rosser E
  replace N1 := N1.MNormal H1s
  replace N2 := N2.MNormal H2s
  simp_all


theorem Tm.Eq.doEta {t1 t2: Tm}:
  t1.Eq t2 -> t1.doEta.Eq t2.doEta
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


theorem Tm.Eq.doEta_inv {t1 t2: Tm}:
  t1.doEta.Eq t2.doEta -> t1.Eq t2
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


theorem Tm.Eq.doEta_same {t1 t2: Tm}:
  t1.Eq t2 ->
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


theorem Tm.Eq.abs_inv {t s: Tm}:
  t.abs.Eq s.abs -> t.Eq s
:= by
  intro E
  apply ECl.rstep
  . apply Tm.abs_up_app_step
  apply ECl.trans
  . apply Tm.Eq.app1
    apply E.up
  apply ECl.inclusion
  apply Tm.abs_up_app_step


theorem Tm.NE.type_unique {Γ: Context} {t: Tm} {T1 T2}:
  NE Γ t T1 -> NE Γ t T2 -> T1 = T2
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
  t.Eq s -> t.BNE -> s.BNE ->
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
  t.Eq s ->
  (NF Γ t T -> NF Γ s T -> t = s) ∧ (NE Γ t T -> NE Γ s T -> t = s)
:= by
  intro E
  induction t generalizing s Γ T with
  | var x =>
    have H: (NE Γ (var x) T -> NE Γ s T -> (var x) = s) := by
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
    have H: (NE Γ (t1.app t2) T -> NE Γ s T -> (t1.app t2) = s) := by
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
        replace E1: t1.Eq s1 := by
          apply Tm.Eq.doEta_inv
          rewrite [E1]
          apply ECl.refl
        replace E2: t2.Eq s2 := by
          apply Tm.Eq.doEta_inv
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
