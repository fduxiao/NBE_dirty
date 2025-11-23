import NBE.SingleSortImp.BetaEtaCons

namespace SingleSortImp.BetaEtaCons
namespace RealPresheaf


structure Presheaf where
  obj: Context -> Type
  weaken {Δ Δ'}: obj Δ -> obj (Δ' ++ Δ)


instance: CoeFun Presheaf (fun _ => Context -> Type) where
  coe P := P.obj


/--
Yoneda embedding `yΓ`
-/
def yoneda (Γ: Context): Presheaf where
  /-
  `yΓ` = `Hom[-, Γ]`, i.e., `{Δ: Context // Σ D, Δ = D ++ Γ}`. Thus, I use `P` as a morphism, while
  if `Δ` is not a prefix of `Γ`, we just choose the result to be none.
  -/
  obj Δ := {D: Context // Δ = D ++ Γ}

  /-
  Given `Δ` and `Δ' ++ Δ`, we have to define the map from `yΓ(Δ)` to `yΓ(Δ' ++ Δ)`.
  For some `D ∈ yΓ(Δ)`, i.e. `Δ = D ++ Γ`, we map it to `Δ' ++ D` so that `Δ' ++ Δ = Δ' ++ D ++ Γ`
  -/
  weaken {Δ Δ'} := by
    rintro ⟨P, E⟩
    exists Δ' ++ P


def yoneda.id {Δ}: (yoneda Δ) Δ := by
  simp [yoneda]
  exists []


def Presheaf.mul (P Q: Presheaf): Presheaf where
  obj Δ := P Δ × Q Δ
  weaken
    | (p, q) => (P.weaken p, Q.weaken q)


@[simp]
def Presheaf.mul_obj {P Q: Presheaf} {Δ}:
  (P.mul Q) Δ = ((P Δ) × (Q Δ))
:= by
  simp [Presheaf.mul]


structure Natural (P Q: Presheaf) where
  component {Δ: Context}: P Δ -> Q Δ


instance {P Q}: CoeFun (Natural P Q) (fun _ => forall {Δ}, P Δ -> Q Δ) where
  coe t := t.component


def Presheaf.imp (P Q: Presheaf): Presheaf where
  /-
  `(P => Q)(Δ) = Hom[yΔ, P => Q] = Hom[yΔ × P, Q] = Nat[yΔ × P, Q]`
  -/
  obj (Δ: Context) := Natural ((yoneda Δ).mul P) Q
  weaken {Δ Δ'} := by
    intro N
    apply Natural.mk
    intro W
    rintro ⟨⟨D, E⟩, p⟩
    apply N.component
    simp
    replace E: W = (D ++ Δ') ++ Δ := by simp_all
    refine ⟨⟨D ++ Δ', E⟩, p⟩


def NE (T: Ty): Presheaf where
  obj Δ := { t: Tm // Tm.NE Δ t T}
  weaken {Δ Δ'} := by
    rintro ⟨t, N⟩
    exists t.up 0 Δ'.length
    apply N.weaken_app


def NE.of {Γ t T}:
  Tm.NE Γ t T -> NE T Γ
:= by
  intro H
  simp [NE]
  exists t


def NF (T: Ty): Presheaf where
  obj Δ := { t: Tm // Tm.NF Δ t T}
  weaken {Δ Δ'} := by
    rintro ⟨t, N⟩
    exists t.up 0 Δ'.length
    apply N.weaken_app


def NF.of {Γ t T}:
  Tm.NF Γ t T -> NF T Γ
:= by
  intro H
  simp [NF]
  exists t


def Sem: Ty -> Presheaf
  | .Atom => NF .Atom
  | .imp T1 T2 => (Sem T1).imp (Sem T2)

mutual

def quote {T: Ty} {Δ: Context}: (Sem T) Δ -> (NF T) Δ :=
  match T with
  | .Atom => by
    simp [Sem]
    apply id
  | .imp A B => by
    simp [NF, Sem, Presheaf.imp]
    intro N
    replace N := N.component (Δ := A :: Δ)
    simp at N
    let H1: yoneda Δ (A :: Δ) := ⟨[A], by simp⟩
    let H2: Sem A (A :: Δ) := by
      apply unquote
      simp [NE]
      exists (.var 0)
      constructor
      simp
    specialize N ⟨H1, H2⟩
    replace N := quote N
    simp [NF] at N
    rcases N with ⟨t, N⟩
    exists t.abs
    apply N.abs


def unquote {T: Ty} {Δ: Context}: (NE T) Δ -> (Sem T) Δ :=
  match T with
  | .Atom => by
    simp [Sem]
    simp [NE, NF]
    rintro ⟨t, N⟩
    exists t
    apply N.atom
  | .imp A B => by
    simp [NE]
    rintro ⟨t, N⟩
    simp [Sem, Presheaf.imp]
    apply Natural.mk
    rintro Γ ⟨⟨D, E⟩, N'⟩
    apply unquote
    simp [NE]
    obtain ⟨s, N'⟩ := quote N'
    exists (t.up 0 D.length).app s
    apply Tm.NE.app
    . rewrite [E]
      apply N.weaken_app
    . exact N'
end


def NF.ofNE {T}: Natural (NE T) (NF T) where
  component N := quote (unquote N)


def NE.normalize {Γ t T}:
  Tm.NE Γ t T -> { t': Tm // Tm.NF Γ t' T }
:= by
  intro N
  replace N := NE.of N
  replace N := NF.ofNE N
  simp [NF] at N
  exact N


def Ty.presheaf (T: Ty): Presheaf where
  obj Δ := Σ t: Tm, Typing Δ t T
  weaken {Δ Δ'} := by
    rintro ⟨t, HT⟩
    exists t.up 0 Δ'.length
    apply HT.weaken_app


def Presheaf.terminal: Presheaf where
  obj _ := Unit
  weaken := id


def Presheaf.List: List Presheaf -> Presheaf
  | [] => Presheaf.terminal
  | P :: PS => P.mul (Presheaf.List PS)


def Context.sem (Γ: Context) := Presheaf.List (List.map Sem Γ)


@[simp]
def Context.sem_nil:
  Context.sem [] = Presheaf.terminal
:= by
  simp [Context.sem, Presheaf.List]


@[simp]
def Context.sem_cons {T TS}:
  Context.sem (T :: TS) = (Sem T).mul (Context.sem TS)
:= by
  simp [Context.sem, Presheaf.List]


def Context.self {Γ}: (Context.sem Γ).obj Γ := by
  match Γ with
  | [] =>
    simp
    exact ()
  | X :: XS =>
    simp
    apply Prod.mk
    . apply unquote
      simp [NE]
      exists (.var 0)
      apply Tm.NE.var
      simp
    . conv =>
        rhs
        change [X] ++ XS
      apply Presheaf.weaken
      apply Context.self


def soundness_var {Γ x T} (HT: Typing Γ (.var x) T) (Δ): (Context.sem Γ) Δ -> (Sem T) Δ := by
  intro F
  match Γ with
  | [] =>
    cases HT
    contradiction
  | X :: XS =>
    simp at F
    obtain ⟨F, FS⟩ := F
    match x with
    | 0 =>
      cases HT with | var HT =>
      simp at HT
      rewrite [<-HT]
      exact F
    | x + 1 =>
      cases HT with | var HT =>
      simp at HT
      apply soundness_var
      . apply Typing.var
        exact HT
      . exact FS


def soundness {Γ t T} (HT: Typing Γ t T): Natural (Context.sem Γ) (Sem T) where
  component {Δ} := by
    intro F
    induction t using Tm.ind generalizing T Γ Δ with
    | var x =>
      apply soundness_var
      . exact HT
      . exact F
    | app t1 t2 IH1 IH2 =>
      cases HT with | app HT1 HT2 =>
      specialize IH1 HT1 F
      specialize IH2 HT2 F
      simp [Sem, Presheaf.imp] at IH1
      replace IH1 := IH1.component (Δ := Δ)
      apply IH1
      simp
      exact ⟨yoneda.id, IH2⟩
    | abs t IH =>
      cases HT with | abs HT =>
      rename_i T1 T2
      simp [Sem, Presheaf.imp]
      apply Natural.mk
      intro Δ'
      simp
      rintro ⟨y, F'⟩
      simp [yoneda] at y
      obtain ⟨D, E⟩ := y
      have K: (Context.sem (T1 :: Γ)).obj Δ' := by
        simp
        apply Prod.mk
        . exact F'
        . rewrite [E]
          apply Presheaf.weaken
          exact F
      specialize IH HT K
      exact IH


def normalize {Γ t T}:
  Typing Γ t T ->
  {t': Tm // Tm.NF Γ t' T}
:= by
  intro HT
  let entailment := soundness HT
  apply quote
  apply entailment.component
  exact Context.self


end RealPresheaf


namespace Example

-- try evaluate them
-- #eval RealPresheaf.normalize cn_2
-- #eval RealPresheaf.normalize ((cn_add.app cn_2).app cn_3)


end Example
