namespace Kripke


abbrev Var := Nat

inductive Formula: Type where
  | atom: Var -> Formula
  | imp: Formula -> Formula -> Formula
  | and: Formula -> Formula -> Formula
  | top: Formula


abbrev Context := List Formula


inductive Context.proves: Context -> Formula -> Prop where
  | var {Γ: Context} {A: Formula}: A ∈ Γ -> Γ.proves A
  | abs {Γ: Context} {A B: Formula}: Context.proves (A :: Γ: Context) B -> Γ.proves (A.imp B)
  | app {Γ: Context} {A B: Formula}: Γ.proves (A.imp B) -> Γ.proves A -> Γ.proves B
  | and {Γ: Context} {A B: Formula}: Γ.proves A -> Γ.proves B -> Γ.proves (A.and B)
  | fst {Γ: Context} {A B: Formula}: Γ.proves (A.and B) -> Γ.proves A
  | snd {Γ: Context} {A B: Formula}: Γ.proves (A.and B) -> Γ.proves B
  | top {Γ: Context}: Γ.proves .top


-- the only thing needed
theorem Context.proves.weaken {Γ Γ': Context} {A: Formula}:
  Γ.proves A ->
  Γ.Sublist Γ' ->
  Γ'.proves A
:= by
  intro H R
  induction H generalizing Γ' with
  | var | abs | app =>
    grind [var, abs, app]
  | and | fst | snd | top =>
    grind [and, fst, snd, top]


-- kripke model
class Kripke (W: Type) where
  rel: W -> W -> Prop
  rel_refl {w: W}: rel w w
  -- rel_antisymm {w1 w2: W}: rel w1 w2 -> rel w2 w1 -> w1 = w2
  rel_trans {w1 w2 w3: W}: rel w1 w2 -> rel w2 w3 -> rel w1 w3

  forces_var: W -> Var -> Prop
  forces_var_inc {w1 w2} {x: Var}: rel w1 w2 -> forces_var w1 x -> forces_var w2 x


def Kripke.forces {W: Type} [inst: Kripke W] (w: W) (A: Formula): Prop :=
  match A with
  | .atom n => inst.forces_var w n
  | .imp P Q => forall w': W, rel w w' -> Kripke.forces w' P -> Kripke.forces w' Q
  | .and P Q => inst.forces w P ∧ inst.forces w Q
  | .top => true


def Forall {A} (P: A -> Prop): List A -> Prop
  | [] => True
  | x :: xs => P x ∧ Forall P xs


@[simp]
theorem Forall.nil {A} {P: A -> Prop}:
  Forall P [] = True
:= by
  simp [Forall]


@[simp]
theorem Forall.cons {A} {P: A -> Prop} {x: A} {xs: List A}:
  Forall P (x :: xs) = (P x ∧ Forall P xs)
:= by
  simp [Forall]


theorem Forall.elem {A} {P: A -> Prop} {x: A} {l: List A}:
  Forall P l -> x ∈ l -> P x
:= by
  intro F E
  induction E with
  | head =>
    simp at F
    exact F.left
  | tail x H IH =>
    simp at F
    apply IH
    exact F.right


theorem Forall.imp {A} {P Q: A -> Prop} {l}:
  Forall P l ->
  (forall x, P x -> Q x) ->
  Forall Q l
:= by
  intro HP H
  induction l with
  | nil =>
    simp
  | cons x xs IH =>
    simp at *
    and_intros
    . apply H
      exact HP.left
    . apply IH
      exact HP.right


def Context.entails (Γ: Context) (A: Formula): Prop := forall {W} (inst: Kripke W),
  forall w: W, Forall (fun B => inst.forces w B) Γ -> inst.forces w A


theorem Kripke.forces_inc {W: Type} [inst: Kripke W] {w w': W} {A}:
  inst.rel w w' -> inst.forces w A -> inst.forces w' A
:= by
  intro R F
  induction A with
  | atom x =>
    simp [Kripke.forces] at *
    apply Kripke.forces_var_inc
    . exact R
    . exact F
  | imp P Q =>
    simp [Kripke.forces]
    intro w'' R' F'
    simp [Kripke.forces] at F
    apply F
    . apply inst.rel_trans
      . exact R
      . exact R'
    . exact F'
  | and P Q IHP IHQ =>
    simp [forces] at *
    grind
  | top =>
    simp [forces]


theorem Context.entails.weaken {Γ: Context} {A B: Formula}:
  Γ.entails B -> entails (A :: Γ) B
:= by
  intro H
  intro W inst w F
  simp at F
  unfold entails at H
  specialize H inst
  apply H
  exact F.right


theorem Context.entails.abs {Γ: Context} {A B: Formula}:
  entails (A :: Γ) B -> Γ.entails (A.imp B)
:= by
  intro E
  intro W inst w Hall
  specialize E inst
  simp [Kripke.forces]
  intro w' R F
  apply E
  simp
  and_intros
  . exact F
  . apply Hall.imp
    intro x
    apply Kripke.forces_inc
    exact R


theorem Context.entails.app {Γ: Context} {A B: Formula}:
  Γ.entails (A.imp B) -> Γ.entails A -> Γ.entails B
:= by
  unfold entails
  intro HAB HA
  intro W inst w Hall
  specialize HAB inst w Hall
  specialize HA inst w Hall
  unfold Kripke.forces at HAB
  specialize HAB w inst.rel_refl
  apply HAB
  exact HA


theorem soundness {Γ: Context} {A: Formula}:
  Γ.proves A -> Γ.entails A
:= by
  intro H
  -- for entail
  unfold Context.entails
  intro W inst w Hall
  induction H generalizing w with
  | var E =>
    replace H := Hall.elem E
    exact H
  | abs P IH =>
    simp [Kripke.forces]
    intro w' R F
    apply IH
    simp
    and_intros
    . exact F
    . apply Hall.imp
      intro x
      apply Kripke.forces_inc
      exact R
  | app H1 H2 IH1 IH2 =>
    specialize IH1 _ Hall
    specialize IH2 _ Hall
    unfold Kripke.forces at IH1
    apply IH1
    . apply Kripke.rel_refl
    . exact IH2
  | and H1 H2 IH1 IH2 =>
    specialize IH1 _ Hall
    specialize IH2 _ Hall
    simp [Kripke.forces]
    and_intros <;> assumption
  | fst H IH | snd H IH =>
    specialize IH _ Hall
    simp [Kripke.forces] at IH
    rcases IH
    assumption
  | top =>
    simp [Kripke.forces]

-- the universal model
instance Context.kripke: Kripke Context where
  rel := List.Sublist
  rel_refl := by
    apply List.Sublist.refl
  -- rel_antisymm := by
    -- admit
  rel_trans := by
    apply List.Sublist.trans
  forces_var w x := w.proves (.atom x)
  forces_var_inc := by
    intros w1 w2 x R H
    apply Context.proves.weaken H
    exact R


def Context.forces (Γ: Context) (A: Formula): Prop := Context.kripke.forces Γ A


@[simp]
theorem Context.forces.atom {Γ: Context} {x: Var}:
  Γ.forces (.atom x) = Context.kripke.forces_var Γ x
:= by
  simp [forces, Kripke.forces]


@[simp]
theorem Context.forces.imp {Γ: Context} {A B: Formula}:
  Γ.forces (A.imp B) = forall Γ': Context, Γ.Sublist Γ' -> Γ'.forces A -> Γ'.forces B
:= by
  simp [forces, Kripke.forces, Kripke.rel]


@[simp]
theorem Context.forces.and {Γ: Context} {A B: Formula}:
  Γ.forces (A.and B) = (Γ.forces A ∧ Γ.forces B)
:= by
  simp only [forces, Kripke.forces]


@[simp]
theorem Context.forces.top {Γ: Context}:
  Γ.forces .top = True
:= by
  simp [forces, Kripke.forces]


theorem Context.forces_iff_proves {Γ: Context} {A: Formula}:
  Γ.forces A <-> Γ.proves A
:= by
  induction A generalizing Γ with
  | atom x =>
    simp [forces, Kripke.forces, Kripke.forces_var]
  | imp T1 T2 IH1 IH2=>
    apply Iff.intro
    . intro F
      simp at F
      apply proves.abs
      apply IH2.mp
      apply F
      . apply List.sublist_cons_self
      . apply IH1.mpr
        apply proves.var
        apply List.mem_cons_self
    . intro P
      simp
      intro Γ' R F
      apply IH2.mpr
      replace IH1 := IH1.mp F
      replace P := P.weaken R
      apply proves.app
      . exact P
      . exact IH1
    | and T1 T2 IH1 IH2 =>
      apply Iff.intro
      . intro F
        simp at F
        apply proves.and <;>
        grind
      . intro P
        simp
        and_intros
        . apply IH1.mpr
          apply proves.fst
          exact P
        . apply IH2.mpr
          apply proves.snd
          exact P
    | top =>
      apply Iff.intro
      . intros
        apply proves.top
      . intros
        simp [forces, Kripke.forces]


theorem completeness {Γ: Context} {A: Formula}:
  Γ.entails A -> Γ.proves A
:= by
  intro H
  apply Context.forces_iff_proves.mp
  simp [Context.entails] at H
  specialize H Context.kripke Γ
  apply H
  clear H A
  induction Γ with
  | nil =>
    simp
  | cons x xs IH =>
    simp
    and_intros
    . apply Context.forces_iff_proves.mpr
      apply Context.proves.var
      apply List.mem_cons_self
    . apply IH.imp
      intro y H
      replace H := Context.forces_iff_proves.mp H
      apply Context.forces_iff_proves.mpr
      apply Context.proves.weaken H
      apply List.sublist_cons_self
