import NBE.SingleSortImp.Presheaf
import NBE.SingleSortImp.BetaEta
namespace SingleSortImp
namespace BetaEtaCons



def forces (P: Context -> Tm -> Ty -> Type) (Γ: Context) (t: Tm) (T: Ty) :=
match T with
| .Atom =>
  P Γ t T
| .imp A B =>
  forall (s: Tm) Γ',
    forces P (Γ' ++ Γ) s A ->
    forces P (Γ' ++ Γ) ((t.up 0 Γ'.length).app s) B


def NF (Γ: Context) (t: Tm) (T: Ty): Type := {t': Tm // t.eq t' ∧ Tm.NF Γ t' T}
def NE (Γ: Context) (t: Tm) (T: Ty): Type := {t': Tm // t.eq t' ∧ Tm.NE Γ t' T}


def NE.var {Γ A}: NE (A :: Γ) (Tm.var 0) A := by
  simp [NE]
  exists (.var 0)
  and_intros
  . apply ECl.refl
  . constructor
    simp


def N_imp {Γ Γ' t s A B}:
  NE Γ t (A.imp B) ->
  NF (Γ' ++ Γ) s A ->
  NE (Γ' ++ Γ) ((Tm.up 0 (List.length Γ') t).app s) B
:= by
  rintro ⟨t', Et, Nt⟩
  rintro ⟨s', Es, Ns⟩
  exists (t'.up 0 Γ'.length).app s'
  and_intros
  . apply Tm.eq.app
    . exact Et.up
    . exact Es
  . apply Tm.NE.app
    . apply Nt.weaken_app
    . exact Ns


mutual

def quote {Γ t T}: forces NF Γ t T -> NF Γ t T :=
  match T with
  | .Atom => by
    simp [forces]
    intro N
    exact N
  | .imp T1 T2 => by
    simp [forces]
    intro F
    specialize F (.var 0) [T1]
    simp at F
    specialize F (unquote NE.var)
    obtain ⟨t', E, N⟩ := quote F
    exists t'.abs
    and_intros
    . apply ECl.rstep Tm.step.eta
      apply Tm.eq.abs
      exact E
    . apply Tm.NF.abs
      exact N


def unquote {Γ t T}: NE Γ t T -> forces NF Γ t T :=
  match T with
  | .Atom => by
    simp [forces]
    rintro ⟨t', E, N⟩
    exists t'
    and_intros
    . exact E
    . apply Tm.NF.atom
      exact N
  | .imp T1 T2 => by
    intro N
    simp [forces]
    intro s Γ' F
    obtain F := quote F
    apply unquote
    apply N_imp
    . exact N
    . exact F
end


def NE.normalize {Γ t T}:
  Tm.NE Γ t T -> { t': Tm // t.eq t' ∧ Tm.NF Γ t' T }
:= by
  intro N
  replace N: NE Γ t T := by
    exists t
    and_intros
    . apply ECl.refl
    . exact N
  replace N := unquote N
  replace N := quote N
  exact N


namespace Example

def Γ: Context := [.Atom, .imp .Atom .Atom]

def var0_NE: Tm.NE Γ (.var 0) .Atom := by
  constructor
  simp [Γ]


def var1_NE: Tm.NE Γ (.var 1) (.imp .Atom .Atom) := by
  constructor
  simp [Γ]

def var1' := (NE.normalize var1_NE).property
end Example


inductive Satisfy (Δ: Context): Env -> Context -> Type where
  | nil: Satisfy Δ [] []
  | cons {T: Ty} {t: Tm} {Γ ts}:
    forces NF Δ t T ->
    Satisfy Δ ts Γ ->
    Satisfy Δ (t :: ts) (T :: Γ)


theorem Satisfy.length {Δ env Γ}:
  Satisfy Δ env Γ -> env.length = Γ.length
:= by
  intro S
  induction S with
  | nil =>
    simp
  | cons =>
    simp_all


def forces.weaken {Γ Γ' t T}:
  forces NF Γ t T -> forces NF (Γ' ++ Γ) (t.up 0 Γ'.length) T
:= by
  intro F
  induction T using Ty.ind generalizing Γ' with
  | Atom =>
    simp [forces]
    obtain ⟨t', E, N⟩ := F
    exists (t'.up 0 Γ'.length)
    and_intros
    . apply E.up
    . apply N.weaken_app
  | imp A B IH1 IH2 =>
    simp [forces]
    intro s Γ'' F'
    simp [Tm.shift_up_add]
    rewrite [<-List.append_assoc]
    rewrite [Nat.add_comm]
    rewrite [<-List.length_append]
    apply F
    simp
    exact F'


def Satisfy.weaken {Δ Δ': Context} {Γ env}:
  Satisfy Δ env Γ -> Satisfy (Δ' ++ Δ) (env.up 0 Δ'.length) Γ
  | .nil => .nil
  | .cons F S => .cons F.weaken S.weaken


def Satisfy.weaken_cons {Δ A} {Γ env}:
  Satisfy Δ env Γ -> Satisfy (A :: Δ) (env.up 0 1) Γ
:= by
  intro S
  replace S := S.weaken (Δ' := [A])
  simp at S
  exact S


def Satisfy.self {Γ}:
  Satisfy Γ (Env.vars Γ.length) Γ
:= match Γ with
  | [] => .nil
  | T :: TS => by
    apply Satisfy.cons
    . apply unquote
      apply NE.var
    . apply Satisfy.weaken_cons
      apply Satisfy.self


theorem Satisfy.some_lt {Γ i T} {Δ env}:
  Satisfy Δ env Γ ->
  Γ.lookup i = some T ->
  i < env.length
:= by
  intro S H
  simp_all [S.length]
  apply FinMap.lookup_some_lt H


/--
I have to redefine this in order to have the constructive proof.
-/
inductive Typing: Context -> Tm -> Ty -> Type where
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


def Typing.weaken_lemma {Γ1 Γ2 Γ3: Context} {M: Tm} {T}:
  Typing (Γ1 ++ Γ2) M T ->
  Typing (Γ1 ++ (Γ3 ++ Γ2)) (M.up Γ1.length Γ3.length) T
:= by
  intro HT
  induction M using Tm.ind generalizing Γ1 Γ2 Γ3 T with
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
    exact HT
  | app M1 M2 IH1 IH2 =>
    cases HT with | app H1 H2 =>
    simp [Tm.up]
    constructor
    . apply IH1
      exact H1
    . apply IH2
      exact H2


def Typing.weaken_app {Γ1 Γ2: Context} {M: Tm} {T}:
  Typing Γ1 M T ->
  Typing (Γ2 ++ Γ1) (M.up 0 Γ2.length) T
:= by
  intro H
  conv at H =>
    arg 1
    change [] ++ Γ1
  conv =>
    pattern (Γ2 ++ Γ1)
    change [] ++ (Γ2 ++ Γ1)
  apply weaken_lemma
  exact H


theorem Typing.bound {Γ: Context} {t T}:
  Typing Γ t T -> t.bound ≤ Γ.length
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


def soundness_var {Δ Γ: Context} {i} {env: Env} {T}:
  (H: Γ.lookup i = some T) ->
  (S: Satisfy Δ env Γ) ->
  forces NF Δ (env[i]'(by apply S.some_lt H)) T
:= by
  intro H S
  match env with
  | [] =>
    cases S
    contradiction
  | x :: xs =>
    match i with
    | 0 =>
      simp
      match Γ with
      | [] => contradiction
      | T :: Ts =>
        simp_all
        cases S with | cons F _ =>
        rewrite [<-H]
        exact F
    | i + 1 =>
      simp_all
      match Γ with
      | [] => contradiction
      | T :: Ts =>
        simp at H
        cases S with | cons F S =>
        apply soundness_var H S


def forces_eq {Γ: Context} {t1 t2: Tm} {T: Ty}:
  t1.eq t2 -> forces NF Γ t1 T -> forces NF Γ t2 T
:= by
  intro E F
  induction T using Ty.ind generalizing t1 t2 Γ with
  | Atom =>
    unfold forces at *
    obtain ⟨t', E', H⟩ := F
    exists t'
    and_intros
    . apply ECl.trans
      . apply ECl.symm
        exact E
      . exact E'
    . exact H
  | imp T1 T2 IH1 IH2 =>
    simp [forces]
    intro s Γ' F'
    apply IH2
    . apply Tm.eq.app1
      apply E.up
    . specialize F s Γ'
      apply F
      exact F'


def soundness {Γ: Context} {t T}:
  Typing Γ t T ->
  forall Δ env, Satisfy Δ env Γ -> forces NF Δ (t.msubst env) T
:= by
  intro HT Δ env S
  induction t using Tm.ind generalizing Γ T Δ env with
  | var x =>
    cases HT with | var H =>
    simp [Tm.msubst, Tm.msubst_var_lt (S.some_lt H)]
    apply soundness_var H S
  | app t1 t2 IH1 IH2 =>
    cases HT with | app HT1 HT2 =>
    rename_i A
    specialize IH1 HT1 _ _ S
    specialize IH2 HT2 _ _ S
    simp [Tm.msubst]
    simp [forces] at IH1
    specialize IH1 (t2.msubst env) []
    simp at IH1
    apply IH1
    exact IH2
  | abs t IH =>
    cases HT with | abs HT =>
    rename_i T1 T2
    specialize IH HT
    simp [forces]
    intro s Δ' F
    obtain ⟨s', E, N⟩ := quote F
    have K: Satisfy (Δ' ++ Δ) (s :: env.up 0 Δ'.length) (T1 :: Γ) := by
      apply Satisfy.cons
      . exact F
      . apply Satisfy.weaken
        exact S
    specialize IH _ _ K
    apply forces_eq
    . apply ECl.symm
      apply ECl.inclusion
      apply Tm.step.compute
      apply Tm.step.appAbs
      apply Tm.msubst_le_step
      replace HT := HT.bound
      simp at HT
      replace S := S.length
      rewrite [S]
      exact HT
    . exact IH


def normalize {Γ t T}:
  Typing Γ t T ->
  {t': Tm // t.eq t' ∧ Tm.NF Γ t' T}
:= by
  intro HT
  let entailment := soundness HT
  specialize entailment Γ (Env.vars Γ.length) (Satisfy.self)
  simp at entailment
  apply quote entailment


namespace Example


def var1: Typing Γ (.var 1) (.imp .Atom .Atom) := by
  constructor
  simp [Γ]


scoped macro "typing": tactic => `(tactic| repeat (constructor <;> try (simp; eq_refl)))

def varApp (n: Nat): Tm -> Tm := (Tm.var n).app


def ChurchNum: Ty := (Ty.Atom.imp Ty.Atom).imp (Ty.Atom.imp Ty.Atom)


def cn_2: Typing [] (.abs $ .abs $ varApp 1 $ varApp 1 $ (.var 0)) ChurchNum := by
  typing


def cn_3: Typing [] (.abs $ .abs $ varApp 1 $ varApp 1 $ varApp 1 $ (.var 0)) ChurchNum := by
  typing


/--
λc₁.λc₂.(λs.λz. c₂ s (c₁ s z))
 3   2    1  0. (2  1) ((3  1) 0)
-/
def cn_add: Typing []
  (.abs $ .abs $ .abs $ .abs $ (varApp 2 (.var 1)).app ((varApp 3 (.var 1)).app (.var 0)))
  (ChurchNum.imp (ChurchNum.imp ChurchNum))
:= by
  typing


-- try evaluate them
-- #eval normalize cn_2
-- #eval normalize ((cn_add.app cn_2).app cn_3)


end Example
