texttt{.lean file}}

  }}



pagecolor{Purple}

begin{center}

 
 
 
 

def n : Int := 1


def reflexivity {X : Type} {x : X} (p : x = x) := Eq.refl p
def symmetry {X : Type} {x : X} {y : X}  (p : x = y) := Eq.symm p
def transitivity {X : Type} {x : X} {y : X} {z : X} (p : x = y) (q : y = z) := Eq.trans p q
notation p "|" q => transitivity p q


def extensionality (f g : X → Y) (p : (x:X) → f x = g x) : f = g := funext p


def equal_arguments {X : Type} {Y : Type} {a : X} {b : X} (f : X → Y) (p : a = b) : f a = f b := congrArg f p

def equal_functions {X : Type} {Y : Type} {f₁ : X → Y} {f₂ : X → Y} (p : f₁ = f₂) (x : X) : f₁ x = f₂ x := congrFun p x


-- A category C consists of:
structure category where
  Obj : Type u
  Hom : Obj → Obj → Type v
  Idn : (X:Obj) → Hom X X
  Cmp : (X:Obj) → (Y:Obj) → (Z:Obj) → (_:Hom X Y) → (_:Hom Y Z) → Hom X Z
  Id₁ : (X:Obj) → (Y:Obj) → (f:Hom X Y) → 
    Cmp X Y Y f (Idn Y) = f
  Id₂ : (X:Obj) → (Y:Obj) → (f:Hom X Y) → 
    Cmp X X Y (Idn X) f = f
  Ass : (W:Obj) → (X:Obj) → (Y:Obj) → (Z:Obj) → (f:Hom W X) → (g:Hom X Y) → (h:Hom Y Z) →
    (Cmp W X Z) f (Cmp X Y Z g h) = Cmp W Y Z (Cmp W X Y f g) h


-- Notation for the identity map which infers the category:
def identity_map {C : category} (X : C.Obj) := C.Idn X
notation "𝟙" => identity_map

-- Notation for the domain of a morphism:
def Dom {C : category} {X : C.Obj} {Y : C.Obj} (_ : C.Hom X Y) := X

-- Notation for the codomain of a morphism:
def Cod {C : category} {X : C.Obj} {Y : C.Obj} (_ : C.Hom X Y) := X

-- Notation for composition which infers the category and objects:
def composition {C : category} {X : C.Obj} {Y : C.Obj} {Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) : C.Hom X Z := C.Cmp X Y Z f g
notation g "∘" f => composition f g


-- obtaining a morphism from an equality
def Map {C : category} {X : C.Obj} {Y : C.Obj} (p : X = Y) : C.Hom X Y := by
subst p
exact C.Idn X


-- definition of an isomorphism from X to Y
structure isomorphism {C : category} (X : C.Obj) (Y : C.Obj) where
  Fst : C.Hom X Y
  Snd : C.Hom Y X
  Id₁ : (Fst ∘ Snd) = 𝟙 Y
  Id₂ : (Snd ∘ Fst) = 𝟙 X


-- notation for isomorphisms from X to Y (≅)
notation X "≅" Y => isomorphism X Y


-- defining the inverse of an isomorphism between objects X and Y
def inverse {C : category} {X : C.Obj} {Y : C.Obj} (f : X ≅ Y) : Y ≅ X := {Fst := f.Snd, Snd := f.Fst, Id₁ := f.Id₂, Id₂ := f.Id₁}


-- notation for inverse : isos from X to Y to isos from Y to X
notation f "⁻¹" => inverse f


-- defining the objects of the category Set
def SetObj : Type 1 := Type

-- defining the morphisms of the category Set
def SetHom (X : SetObj) (Y : SetObj) : Type := X → Y

-- defining the identity morphism of an object in the category Set
def SetIdn (X : SetObj) : SetHom X X := λ (x : X) => x

--  defining composition in the category Set
def SetCmp (X : SetObj) (Y : SetObj) (Z : SetObj) (f : SetHom X Y) (g : SetHom Y Z) : (SetHom X Z) := λ (x : X) => (g (f x)) 


-- proving the first identity law for composition in Set
def SetId₁ (X : SetObj) (Y : SetObj) (f : SetHom X Y) : SetCmp X Y Y f (SetIdn Y) = f := sorry

-- proving the second identity law for composition in Set
def SetId₂ (X : SetObj) (Y : SetObj) (f : SetHom X Y) : SetCmp X X Y (SetIdn X) f = f := sorry

-- proving the associativity law for composition in Set
def SetAss (W : SetObj) (X : SetObj) (Y : SetObj) (Z : SetObj) (f : SetHom W X) (g : SetHom X Y) (h : SetHom Y Z) : SetCmp W X Z f (SetCmp X Y Z g h) = SetCmp W Y Z (SetCmp W X Y f g) h := sorry


-- defining the category Set
def Set : category := {Obj := SetObj, Hom := SetHom, Idn := SetIdn, Cmp := SetCmp, Id₁ := SetId₁, Id₂ := SetId₂, Ass := SetAss}


-- definition of a functor
structure functor (C : category) (D : category) where
   Obj : ∀(_ : C.Obj),D.Obj
   Hom : ∀(X : C.Obj),∀(Y : C.Obj),∀(_ : C.Hom X Y),D.Hom (Obj X) (Obj Y)
   Idn : ∀(X : C.Obj),Hom X X (C.Idn X) = D.Idn (Obj X)
   Cmp : ∀(X : C.Obj),∀(Y : C.Obj),∀(Z : C.Obj),∀(f : C.Hom X Y),∀(g : C.Hom Y Z),
   D.Cmp (Obj X) (Obj Y) (Obj Z) (Hom X Y f) (Hom Y Z g) = Hom X Z (C.Cmp X Y Z f g)


-- notation for the type of Hom from a category C to a category D
notation C "➞" D => functor C D


-- Notation for the domain of a functor:
def domain {C : category} {X : C.Obj} {Y : C.Obj} (_ : C.Hom X Y) := X
notation "𝗗𝗼𝗺" => domain


-- Notation for the domain of a functor:
def codomain {C : category} {X : C.Obj} {Y : C.Obj} (_ : C.Hom X Y) := Y
notation "𝗖𝗼𝗱" => codomain


-- definition of the identity functor on objects
def CatIdnObj (C : category) := 
fun(X : C.Obj)=>
X

-- definition of the identity functor on morphisms
def CatIdnMor (C : category) := 
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(f : C.Hom X Y)=>
f

-- proving the identity law for the identity functor
def CatIdnIdn (C : category) := 
fun(X : C.Obj)=>
Eq.refl (𝟙 X)

-- proving the compositionality law for the identity functor 
def CatIdnCmp (C : category) := 
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(Z : C.Obj)=>
fun(f : C.Hom X Y)=>
fun(g : C.Hom Y Z)=>
Eq.refl (g ∘ f)

-- defining the identity functor
def CatIdn (C : category) : functor C C := 
{Obj := CatIdnObj C, Hom := CatIdnMor C, Idn := CatIdnIdn C, Cmp := CatIdnCmp C}


-- notation for the identity functor
notation "𝟭" => CatIdn


-- defining the composition G ∘ F on objects
def CatCmpObj (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) := 
fun(X : C.Obj)=>
(G.Obj (F.Obj X))

-- defining the composition G ∘ F on morphisms
def CatCmpHom (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) := 
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(f : C.Hom X Y)=>
(G.Hom) (F.Obj X) (F.Obj Y) (F.Hom X Y f)

-- proving the identity law for the composition G ∘ F
def CatCmpIdn (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) := 
fun(X : C.Obj)=> 
(congrArg (G.Hom (F.Obj X) (F.Obj X)) (F.Idn X) ) | (G.Idn (F.Obj X))

-- proving the compositionality law for the composition G ∘ F
def CatCmpCmp (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) := 
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(Z : C.Obj)=>
fun(f : C.Hom X Y)=>
fun(g : C.Hom Y Z)=>
((Eq.trans) 
(G.Cmp (F.Obj X) (F.Obj Y) (F.Obj Z) (F.Hom X Y f) (F.Hom Y Z g)) 
(congrArg (G.Hom  (F.Obj X) (F.Obj Z)) (F.Cmp X Y Z f g)))

-- defining the composition in the category Cat
def CatCmp (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) : functor C E := 
{Obj := CatCmpObj C D E F G, Hom := CatCmpHom C D E F G,Idn := CatCmpIdn C D E F G, Cmp := CatCmpCmp C D E F G }


-- notation for the composition in the category Cat
def functor_composition {C : category} {D : category} {E : category} (F : functor C D) (G : functor D E) : functor C E := CatCmp C D E F G
notation G "•" F => functor_composition F G
/-
-- this should be able to handle F • X or F • G
-/


-- proving Cat.Id₁
def CatId₁ (C : category) (D : category) (F : functor C D) : ((CatCmp C D D) F (CatIdn D) = F) := Eq.refl F


-- Proof of Cat.Id₂
def CatId₂ (C : category) (D : category) (F : functor C D) : ((CatCmp C C D) (CatIdn C) F = F) := Eq.refl F


-- Proof of Cat.Ass
def CatAss (B : category) (C : category) (D : category) (E : category) (F : functor B C) (G : functor C D) (H : functor D E) : (CatCmp B C E F (CatCmp C D E G H) = CatCmp B D E (CatCmp B C D F G) H) := 
Eq.refl (CatCmp B C E F (CatCmp C D E G H))


-- The category of categories
def Cat : category := {Obj := category, Hom := functor, Idn := CatIdn, Cmp := CatCmp, Id₁:= CatId₁, Id₂:= CatId₂, Ass := CatAss}


/-
def OppObjObj (C : category) := C.Obj
def OppObjHom (C : category) (X : OppObjObj) (Y : OppObjObj) := C.Hom Y X
def OppObjIdn (C : category) (X : OppObjObj) := C.Idn X
def OppObjCmp (C : category) (X : OppObjObj) (Y : OppObjObj) (Z : OppObjObj) (f : OppObjHom X Y) (g : OppObjHom Y Z) : OppObjHom X Z := 
-/
-- def OppObj (C : category) : category := {Obj := OppObjObj, Hom := OppObjHom, Idn := OppObjIdn, Cmp := OppObjCmp}


/-
def OppHomObj (C : category) (D : category) (F : functor C D) 
def OppHomHom (C : category) (D : category) (F : functor C D) 
def OppHomIdn (C : category) (D : category) (F : functor C D) 
def OppHomCmp (C : category) (D : category) (F : functor C D) 
def OppHom (C : category) (D : category) (F : functor C D) 
-/


/-
def OppIdn
-/


/-
def OppCmp
-/


def Opp : Cat ➞ Cat := sorry --{}


notation C "ᵒᵖ" => Opp.Obj C


-- defining the objects of the Prd C × D
def PrdObjObj (C : category) (D : category) := (C.Obj) × (D.Obj)

-- defining the morphisms of C × D
def PrdObjHom (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) := (C.Hom X.1 Y.1) × (D.Hom X.2 Y.2)

-- defining the identity functor on an object in C × D
def PrdObjIdn (C : category) (D : category) (X : PrdObjObj C D) := ((C.Idn X.1),(D.Idn X.2))

-- defining the composition on morphisms in C × D
def PrdObjCmp (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (Z : PrdObjObj C D) (f : PrdObjHom C D X Y) (g : PrdObjHom C D Y Z) : PrdObjHom C D X Z := (g.1 ∘ f.1, g.2 ∘ f.2)


-- proving the first identity law for morphisms in C × D 
theorem PrdObjId₁ (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (f : PrdObjHom C D X Y) :
  PrdObjCmp C D X Y Y f (PrdObjIdn C D Y) = f  := sorry

/-
-- Eq.trans (PrdObjId₁₀ C D X Y f) (Eq.trans (PrdObjId₁₁ C D X Y f) (PrdObjId₁₂ C D X Y f))

theorem PrdObjId₁₀ (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (f : PrdObjHom C D X Y) :
  PrdCmp C D X Y Y f (PrdIdn C D Y) = (C.Cmp X.1 Y.1 Y.1 f.1 (C.Idn Y.1), D.Cmp X.2 Y.2 Y.2 f.2 (D.Idn Y.2)) := Eq.refl (C.Cmp X.1 Y.1 Y.1 f.1 (C.Idn Y.1), D.Cmp X.2 Y.2 Y.2 f.2 (D.Idn Y.2))
theorem PrdObjId₁₁ (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (f : PrdObjHom C D X Y) :
  (C.Cmp X.1 Y.1 Y.1 f.1 (C.Idn Y.1), D.Cmp X.2 Y.2 Y.2 f.2 (D.Idn Y.2)) = (f.1, f.2) :=
  by rw [show (f.fst, f.snd) = _ by rw [← C.Id₁ X.1 Y.1 f.1, ← D.Id₁ X.2 Y.2 f.2]]
theorem PrdObjId₁₂ (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (f : PrdObjHom C D X Y) :
  (f.1, f.2) = f := Eq.refl f
-/


-- proving the second identity law for morphisms in C × D 
theorem PrdObjId₂ (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (f : PrdObjHom C D X Y) : PrdObjCmp C D X X Y (PrdObjIdn C D X) f = f  := sorry
/-
-- Eq.trans (PrdObjId₂₀ C D X Y f) (Eq.trans (PrdId₂₁ C D X Y f) (PrdId₂₂ C D X Y f))
theorem PrdId₂₀ (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (f : PrdObjHom C D X Y) :
  PrdCmp C D X X Y (PrdIdn C D X) f = (C.Cmp X.1 X.1 Y.1 (C.Idn X.1) f.1, D.Cmp X.2 X.2 Y.2 (D.Idn X.2) f.2) := 
  Eq.refl (C.Cmp X.1 X.1 Y.1 (C.Idn X.1) f.1, D.Cmp X.2 X.2 Y.2 (D.Idn X.2) f.2)
theorem PrdId₂₁ (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (f : PrdObjHom C D X Y) :
  (C.Cmp X.1 X.1 Y.1 (C.Idn X.1) f.1, D.Cmp X.2 X.2 Y.2 (D.Idn X.2) f.2) = (f.1, f.2) :=
  by rw [show (f.fst, f.snd) = _ by rw [← C.Id₂ X.1 Y.1 f.1, ← D.Id₂ X.2 Y.2 f.2]]
theorem PrdId₂₂ (C : category) (D : category) (X : PrdObjObj C D) (Y : PrdObjObj C D) (f : PrdObjHom C D X Y) :
  (f.1, f.2) = f := Eq.refl f
-/


-- proving associativity for morphisms in C × D
theorem PrdObjAss (C : category) (D : category) (W : PrdObjObj C D) (X : PrdObjObj C D) (Y : PrdObjObj C D) (Z : PrdObjObj C D) (f : PrdObjHom C D W X) (g : PrdObjHom C D X Y) (h : PrdObjHom C D Y Z) : PrdObjCmp C D W X Z f (PrdObjCmp C D X Y Z g h) = PrdObjCmp C D W Y Z (PrdObjCmp C D W X Y f g) h := sorry


-- defining the PrdObj of two categories
def PrdObj (C : category) (D : category) : category := {Obj := PrdObjObj C D, Hom := PrdObjHom C D, Idn := PrdObjIdn C D, Cmp := PrdObjCmp C D, Id₁ := PrdObjId₁ C D, Id₂:= PrdObjId₂ C D, Ass := PrdObjAss C D}


notation C "⨯_Cat" D => PrdObj C D


-- defining natural transformations for a category C and a category D
structure HomObjHom (C : category) (D : category) (F : functor C D) (G : functor C D) where
  Obj : (X : C.Obj) → (D.Hom (F.Obj X) (G.Obj X))
  Nat : (X : C.Obj) → (Y : C.Obj) → (f : C.Hom X Y) → ((Obj Y) ∘ (F.Hom X Y f) ) = ((G.Hom X Y f) ∘ (Obj X))


-- notation for natural transformations
def natural_transformation {C : category} {D : category} (F : functor C D) (G : functor C D) := HomObjHom C D F G
notation F "⇨" G => natural_transformation F G


-- defining (Hom C D).Idn.Obj for a category C and a category D
def HomObjIdnObj (C : category) (D : category) (F : functor C D) (X : C.Obj) : (D.Hom (F.Obj X) (F.Obj X)) := D.Idn (F.Obj X)

-- defining (Hom C D).Idn.Nat for a category C and a category D
def HomObjIdnNat (C : category) (D : category) (F : functor C D) (X : C.Obj) (Y : C.Obj) (f : C.Hom X Y) : ((HomObjIdnObj C D F Y) ∘ (F.Hom X Y f)) = ((F.Hom X Y f) ∘ (HomObjIdnObj C D F X)) := sorry

-- defining (Hom C D).Idn for a category C and a category D
def HomObjIdn (C : category) (D : category) (F : functor C D) : HomObjHom C D F F := {Obj := HomObjIdnObj C D F, Nat := HomObjIdnNat C D F}


-- defining (Hom C D).Cmp for a category C and a category D
def HomObjCmp (C : category) (D : category) (F : functor C D) (G : functor C D) (H : functor C D) (f : HomObjHom C D F G) (g : HomObjHom C D G H) : HomObjHom C D F H := sorry


-- defining (Hom C D).Id₁
def HomObjId₁ (C : category) (D : category) (F : functor C D) (G : functor C D) (f : HomObjHom C D F G) : HomObjCmp C D F G G f (HomObjIdn C D G) = f := sorry

-- defining (Hom C D).Id₂
def HomObjId₂ (C : category) (D : category) (F : functor C D) (G : functor C D) (f : HomObjHom C D F G) : HomObjCmp C D F F G (HomObjIdn C D F) f = f := sorry

-- defining (Hom C D).Ass
def HomObjAss (C : category) (D : category) (F : functor C D) (G : functor C D) (H : functor C D) (I : functor C D) (α : HomObjHom C D F G) (β : HomObjHom C D G H) (γ : HomObjHom C D H I) : (HomObjCmp C D F G I α (HomObjCmp C D G H I β γ)) = (HomObjCmp C D F H I (HomObjCmp C D F G H α β) γ) := sorry


-- defining the category Hom C D for a category C and a category D
def HomObj (C : category) (D : category) : category := {Obj := functor C D, Hom := HomObjHom C D, Idn := HomObjIdn C D, Cmp := HomObjCmp C D, Id₁ := HomObjId₁ C D, Id₂ := HomObjId₂ C D, Ass := HomObjAss C D}


notation "[" C "," D "]_Cat" => HomObj C D


--  defining F × C on objects
def PrdHomObj (C : category) (D₁ : category) (D₂ : category) (F : D₁ ➞ D₂) (X : PrdObjObj C D₁) : PrdObjObj C D₂ := (X.1, F.Obj X.2)

--  defining F × C on morphisms
def PrdHomHom (C : category) (D₁ : category) (D₂ : category) (F : D₁ ➞ D₂) (G : C ➞ D₁) (H : C ➞ D₁) (g : G ⇨ H) : ((F • G) ⇨ (F • H)) := sorry


--  proving the identity law for F × C
-- def PrdHomIdn (C : category) (D₁ : category) (D₂ : category) (F : D₁ ➞ D₂) (P : PrdObj C D₁) : PrdHom := sorry 

--  proving the compositionality law for F × C
-- def PrdHomCmp (C : category) (D₁ : category) (D₂ : category) (F : D₁ ➞ D₂) (G₁ : C ➞ D₁) (G₂ : C → D₁) (G₃ : C → D₁) (g₁ : G₁ ⇨ G₂) (g₂ : G₂ ⇨ G₃) : ??? := sorry 


-- defining (Prd C).Hom F
-- def PrdHom (C : category) (D₁ : category) (D₂ : category) (F : D₁ ➞ D₂) : (PrdObjObj C D₁) ➞ (PrdObjObj C D₂) := {Obj := PrdHomObj, Hom := PrdHomHom, Idn := PrdHomIdn, Cmp := PrdHomCmp}


-- proving the identity law for Prd C
-- def PrdIdn (C : category) (D : category) : PrdHom C (𝟭 D) = 𝟭 (PrdHom C D) := sorry

--  proving the compositionality law for - ×_Cat C 
--  def PrdCmp (C : category) (D₁ : category) (D₂ : category) (D₃ : category) (F₁ : D₁ ➞ D₂) (F₂ : D₂ ➞ D₃) : ((PrdHom C F₂) • (PrdHom C F₁)) = (F₂ • F₁) := sorry


-- defining the functor C ⨯ - : Cat ➞ Cat
def Prd (C : category) : Cat ➞ Cat := sorry -- {Obj := PrdObj C, Hom := PrdHom C, Idn := PrdIdn C, Cmp := PrdCmp C}


notation "-" "⨯_Cat" C => Prd C


--  defining Hom C F on objects
def HomHomObj (C : category) (D₁ : category) (D₂ : category) (F : functor D₁ D₂) (G : functor C D₁) := Cat.Cmp C D₁ D₂ G F

-- defining Hom C F on morphisms
def HomHomHom (C : category) (D₁ : category) (D₂ : category) (F : functor D₁ D₂) (G₁ : functor C D₁) (G₂ : functor C D₁) (g : G₁ ⇨ G₂) : (F • G₁) ⇨ (F • G₂) := sorry


-- proving the identity law for Hom C F
-- def HomHomIdn (C : category) (D₁ : category) (D₂ : category) (F : functor D₁ D₂) := sorry

--  proving the compositionality law for Hom C F
-- def HomHomCmp := sorry


-- defining Hom C F
-- def HomHom (C : category) (D₁ : category) (D₂ : category) (F : D₁ ➞ D₂) : (HomObj C D₁) ➞ (HomObj C D₂) := sorry 


--  proving the identity law for Hom C
-- def HomIdn (C : category) () :  := sorry

--  proving the compositionality law for Hom C
--  def HomCmp (C : category) () :  := sorry


-- defining the functor Hom C : Cat ➞ Cat
def Hom (C : category) : Cat ➞ Cat := sorry


notation "[" "-" "," C "]_Cat" => Hom C


-- Defining the unit of the prd-hom adjunction
def Pair (C : category) : (𝟭 Cat) ⇨ (Hom C) • (Prd C) := sorry


-- Defining the counit of the prd-hom adjunction
def Eval (C : category) : ((Prd C) • (Hom C)) ⇨ (𝟭 Cat) := sorry


-- first triangle identity of the prd-hom adjunction
/-
-/


-- first triangle identity of the product-hom adjunction
/-
-/


-- ε : X × Y ➞ Y
def Term (X : category) : (Prd X) ⇨ (𝟭 Cat) := sorry
notation "ε" => Term


-- Δ : X × Y ➞ X × X × Y
def Diag (X : category) : (Prd X) ⇨ ((Prd X) • (Prd X)) := sorry


-- notation for the comultiplication for product with X
notation "Δ" => Diag


-- proof of the first identity law of the comultiplication
/-

-/


-- proof of the second identity law of the comultiplication
/-

-/


-- proof of the coassociativity of the comultiplication
/-

-/


-- Construction of the unit for Hom X
def Const : (𝟭 Cat) ⇨ (Hom X) := sorry


-- notation 
/-

-/


-- Construction of the multiplication for [X, -]
def double : (Hom X) ⇨ (Hom X) • (Hom X) := sorry


-- 
/-

-/



-- proving associativity for the comonad (Hom X)
/-

-/


-- proof of the commutativity of categorical Prd
def Tw₁ (C : category) (D : category) : ((Prd C) • (Prd D)) ⇨ ((Prd D) • (Prd C)) := sorry


-- notation "τ₁" => Tw₁


-- proving that the twist map is its own inverse
-- def (C : category) (D : category) : (τ ∘ τ = (Idn (C ⨯ D))) := sorry


-- defining the twist map (Hom X) • (Hom Y) ≅ (Hom Y) • (Hom X)
def Tw₂ (C : category) (D : category) : ((Hom C) • (Hom D)) ⇨ ((Hom D) • (Hom C)) := sorry
-- notation "τ₂" => Twist


-- proof that the twist map is its own inverse
-- def (C : category) (D : category) : (τ ∘ τ = (Idn (C ⨯ D))) := sorry


-- defining the category ⊛
def PntObj : Type := Unit
def PntHom (_ : PntObj) (_ : PntObj) : Type := Unit
def PntIdn (X : PntObj) : PntHom X X := Unit.unit
def PntCmp (X : PntObj) (Y : PntObj) (Z : PntObj) (_ : PntHom X Y) (_ : PntHom Y Z) : PntHom X Z := Unit.unit
def PntId₁ (X : PntObj) (Y : PntObj) (f : PntHom X Y) : PntCmp X Y Y f (PntIdn Y) = f := sorry
def PntId₂ (X : PntObj) (Y : PntObj) (f : PntHom X Y) : PntCmp X X Y (PntIdn X) f = f := sorry
def PntAss (W : PntObj) (X : PntObj) (Y : PntObj) (Z : PntObj) (f : PntHom W X) (g : PntHom X Y) (h : PntHom Y Z) : PntCmp W Y Z (PntCmp W X Y f g) h = PntCmp W X Z f (PntCmp X Y Z g h) := sorry
def Pnt : category := {Obj := PntObj, Hom := PntHom, Idn := PntIdn, Cmp := PntCmp, Id₁ := PntId₁, Id₂ := PntId₂, Ass := PntAss}


-- notation for the category ⊛
notation "⊛" => Pnt


-- defining (Prd ⊛) ⇨ (𝟭 Cat)


-- defining (𝟭 Cat) ⇨ (Prd ⊛)


-- proving the first inverse identity


-- proving the second inverse identity


-- defining (Hom ⊛) ⇨ (𝟭 Cat)
-- def IdnHomObj (C : category) : Hom ⊛ C 
-- def IdnHomHom 
-- def IdnHomIdn
-- def IdnHomCmp


-- defining (𝟭 Cat) ⇨ (Hom ⊛)
-- def IdnHom
-- def 
-- def 
-- def Idn


-- proving the first inverse identity


-- proving the second inverse identity
-- def Hom ⊛ ≅ X


-- Defining the Prd F × G of two Hom one way
def FunPrd₁ {C₁ : category} {C₂ : category} {D₁ : category} {D₂ : category} (F : C₁ ➞ C₂) (G : D₁ ➞ D₂) : (PrdObj C₁ D₁) ➞ (PrdObj C₂ D₂) := sorry


-- Defining the Prd F × G of two Hom the other way
def FunPrd₂ {C₁ : category} {C₂ : category} {D₁ : category} {D₂ : category} (F : C₁ ➞ C₂) (G : D₁ ➞ D₂) : (PrdObj C₁ D₁) ➞ (PrdObj C₂ D₂) := sorry


-- Showing that the two Prds are equal
theorem FunPrdEqn {C₁ : category} {C₂ : category} {D₁ : category} {D₂ : category} (F : C₁ ➞ C₂) (G : D₁ ➞ D₂) : FunPrd₁ F G = FunPrd₂ F G := sorry


-- notation for the functor Prd
notation F "⨯" G => FunPrd₁ F G


-- Defining the canonical map in the universal property of Prd
-- def 


-- Proving the uniqueness of the canonical map in the universal property of Prd
/-
theorem (uniqueness of the canonical map)
-/


-- 
/-

-/


-- definition of a (strict) twocategory
structure twocategory where
  TwoObj : Type
  TwoHom : TwoObj → TwoObj → category
  TwoIdn : (C : TwoObj) → ⊛ ➞ (TwoHom C C)
  TwoCmp : (C : TwoObj) → (D : TwoObj) → (E : TwoObj) → (PrdObj (TwoHom C D) (TwoHom D E)) ➞ (TwoHom C E)
--  TwoId₁ : (C : Obj) → (D : Obj) → (TwoCmp C D D) • ((Idn 1) ⨯ (𝟭 )) = 
--  TwoId₂ : (C : Obj) → (D : Obj) → (Cmp C C D) • ((Idn D) × 1) = 
--  Ass : (B : Obj) → (C : Obj) → (D : Obj) → (E : Obj) → (((Cmp B C E) • (FunPrd₁ (𝟭 (Hom B C)) (Cmp C D E))) = (Cmp B D E • (FunPrd₁ (Cmp B C D) (𝟭 (Hom D E)))))


-- notation for a twocategory
/-

-/


-- defining categories.Idn.Obj
def TwoIdnObj (C : category) (_ : Unit) := Cat.Idn C


-- defining the functor categories.Idn.Hom on morphisms
def TwoIdnHom (C : category) (_ : Unit) (_ : Unit) (_: Unit) := (HomObj C C).Idn (Cat.Idn C)


-- proving the identity law for the functor categories.TwoIdn
-- def TwoIdnIdn (C : category) (_ : Unit) (_ : Unit) (_: Unit) := (HomObj C C).Idn (Cat.Idn C)


-- proving compositionality for the functor categories.TwoIdn
-- def Two.Idn.Cmp (C : category) (_ : Unit) (_ : Unit) (_: Unit) := (HomObj C C).Idn (Cat.Idn C)


-- def categories.Idn
def TwoIdn (C : category) : ⊛ ➞ (HomObj C C) := sorry


--  defining Two.Cmp.Obj
/-
-/


--  defining Two.Cmp.Hom
/-
def TwoTwoHom (C : Obj) (D : Obj) (E : Obj)  : FG.1 FG.2
def TwoTwoHom (C : Obj) (D : Obj) (E : Obj) (f : ((Hom C D) ⨯ (Hom D E)).Hom )
def CatsHom (C : Obj) (D : Obj) (E : Obj) 
(F₁G₁ : ((Hom C D) ⨯ (Hom D E)).Obj) (F₂G₂ : ((Hom C D) ⨯ (Hom D E)).Obj)
-/



-- proving the identity law equation for Two.TwoCmp
/-
def 
-/


-- proving compositionality for the functor Two.Cmp
-- def TwoCmpCmp : (C : category) → (D : category) → (E : category) → (PrdObj (HomObj C D) (HomObj D E)) ➞ (HomObj C E) := sorry


--  Two.Cmp : (C : Obj) → (D : Obj) → (E : Obj) → (Hom C D) × (Hom D E) ➞ (Hom C E)    
def TwoCmp : (C : category) → (D : category) → (E : category) → (PrdObj (HomObj C D) (HomObj D E)) ➞ (HomObj C E) := sorry


--  Id₁ : (C : Obj) → (D : Obj) → (Cats.Id₁)
/-
def TwoId₁ : (C : category) → (D : category) → (F : functor C D) → 
-/


--  Id₂ : (C : Obj) → (D : Obj) → (F : (Hom C D).Obj) → ...      (Cats.Id₁)
/-
def TwoId₂ : (C : category) → (D : category) → (F : functor C D) → 
-/


-- proving associativity of composition for the twocategory of Two
/-
def TwoAss
-/


-- notation for horizontal composition
/-
class horizontal_composition (C : category) (D : category) (E : category) (F₁ : C ➞ D) (F₂ : C → D) (G₁ : D → D) (G₂ : D → E) where
  f : (F₁ ⇨ F₂) → (G₁ ⇨ G₂) → ((G₁ • F₁) ⇨ (G₂ • F₂)) 

def f (p : Prop) : Prop := ¬p
def g (n : Nat): Nat := n + 1
-/


/-
class Elephant (T : Type) where
  fn : T → T

instance prop_elephant : Elephant Prop where
  fn := f

instance int_elephant : Elephant Nat where
  fn := g

def elephant {T : Type} [E : Elephant T] (t : T) : T := E.fn t

#check elephant (2 : Nat)
#reduce elephant (2 : Nat)
#eval elephant (2 : Nat)

#check elephant True
#reduce elephant True

#check elephant (0 : Nat)

notation "𓃰" t => elephant t
#eval 𓃰 (2 : Nat)
-/


/-
class composition (C : category) (D : category) (F : functor C D) (X : Type p₁) (Y : Type p₂) (T : Type p₁ → Type p₂ → Type p₃) (Z : T X Y) where
  f : X → Y → Z

instance functor_application_on_objects (C : category) (D : category) : composition (functor C D) C.Obj (Type p₃) D.Obj where
  f := fun(F : functor C D) => fun(X : C.Obj) => F.Obj X

instance functor_application_on_morphisms (C : category) (D : category) (X : C.Obj) (Y : C.Obj) : composition (functor C D) () () where
  f := 

instance functor_composition

instance natural_transformation_whisker₁

instance natural_transformation_whisker₂

instance horizontal_composition 

-/

/-
notation X × Y => horizontal_composition X Y


notation "𓃰" t => elephant t
#eval 𓃰 (2 : Nat)
-/


-- definition of the yoneda embedding
def yoneda_embedding (C : category) : Cᵒᵖ ➞ Set := sorry


-- notation for the Yoneda embedding
notation "よ" => yoneda_embedding


-- definition of the contravariant yoneda embedding
/-

-/


/-
def (C : category) (F : Cᵒᵖ ⇨ Set) : [X, -] ⇨ F ≅ F • X := sorry
-/


/-
def (C : category) (F : Cᵒᵖ ⇨ Set) : [X, -] ⇨ F ≅ F • X := sorry
-/


/-
def ([X, -] ⇨ [Y, -]) ≅ [X, Y]
-/


/-
def ([-, X] ⇨ [-, Y]) ≅ [Y, X]
-/


-- corollary: the Yoneda embedding is full
/-

-/


-- corollary: the Yoneda embedding is faithful
/-

-/


-- corollary: the contravariant Yoneda embedding is full and faithful
/-

-/


-- definition of an adjunction
structure adjunction where
  C : category
  D : category
  F  : C ➞ D
  G  : D ➞ C
  Unit  : (𝟭 C) ⇨ (G • F)
  Counit  : (F • G) ⇨ (𝟭 D) 
 -- τ₁  : ((𝟭 F) ∙ η)  =  ((𝟭 F) ∙ η)   -- ∘ (Iso (ℂ𝕒𝕥.Hom Dom Cod) (Ass F G F)) ∘ (((CatHom C D).Idn F) • η)) = (CatHom D C).Idn left
--  τ₂  : (𝟙 F) = (𝟙 F)   -- ∘ (Iso (ℂ𝕒𝕥.Hom Dom Cod) (Ass F G F)) ∘ (((CatHom C D).Idn F) • η)) = (CatHom D C).Idn left


-- notation for an adjunction
/-
notation C "" D => adjoint C D --adjoint symbol
def F (U : TwoCat) {C : U.Obj} {D : U.Obj} (f : Adj C D) := f.F

notation f "ॱ" => F f

def G (U : TwoCat) {C : U.Obj} {D : U.Obj} (f : Adj C D) := f.G
notation f "𛲔" => G f

def adjoint {C : category} {D : category} (F : )...

notation F "⊣" G => adjoint 
-/


-- definition of a monad
structure monad where
  C : category
  T : C ➞ C
  Unit : (𝟭 C) ⇨ T
  Mult : (T • T) ⇨ T
--  Id₁  : μ ∘ (η ∙ (𝟙 T)) = 𝟙 T
--  Id₂  : μ ∘ ((𝟙 T) • η) = 𝟙 T
--  Ass  : μ ∘ (μ • (𝟙 T)) = μ ∘ ((𝟙 T) • μ)


-- notation for a monad
/- 
-- notation for monad application
instance comonad_application {C : CatObj} : horizontalCmp (Com C) (Obj C) (Obj C) where
  φ := fun(T₀ : Com C)=>fun(X₀ : Obj C)=>(T₀.functor.Obj X₀)
-/


-- definition of a comonad (shouldn't depend on a twocat)
structure comonad where
  C : category
  T : C ➞ C
  Counit : T ⇨ (𝟭 C)
  Comult : T ⇨ (T • T) 
--  Id₁  : (Unt × (Idn T)) • Comul  = (Idn T)
--  Id₂  : ((Idn T) × Unt) • Comul  = (Idn T)
--  Ass  : (Mul × (Idn T)) • (Idn T) = ((Idn T) × Mul) • (Idn T)



-- notation for a comonad
/-
def Unit {C : category} (M : comonad C) := M.Counit
notation "τ" M => Counit M

def ult {C : category} (M : comonad C) := M.Comult
notation "δ" M => Mlt M

-- notation for monad application
instance comonad_application {C : category} : horizontalCmp (Com C) (Obj C) (Obj C) where
  φ := fun(T₀ : Com C)=>fun(X₀ : Obj C)=>(T₀.functor.on_objects X₀)
-- τ₁
-- τ₂
-- γ
-/


-- the monad corresponding to an adjunction
-- def 



-- notation for the monad corresponding to an adjunction
/-
notation
-/


-- canonical map from eilenberg moore category of the corresponding monad for an adjunction
/-
def
-/


-- notation for the canonical map from eilenberg moore category of the corresponding monad for an adjunction
/-
notation ?
-/


-- the eilenberg moore adjunction unit 
/-
def 
-/


-- eilenberg moore adjunction triangle identity 1
/-
theorem
-/


-- eilenberg moore adjunction triangle identity 2
/-
theorem
-/

-- LEAN: def when ! is an iso (monadicity)
/-
def Monadic (f : Adj) : Prop := sorry
-/
-- defining premonadicity
/-
def Premonadic (f : Adj) : Prop := sorry
-/

-- the comonad corresponding to an adjunction
/-
def
-/


-- notation for the comonad corresponding to an adjunction
/-
notation !
-/


-- canonical map into the coeilenberg comoore category of the corresponding comonad
/-
def
-/


-- notation for canonical map into coeilenberg comoore category of the corresponding monad for an adjunction
/-
notation ?
-/


-- the coeilenberg comoore adjunction unit
/-
def
-/


-- the coeilenberg comoore adjunction counit
/-
def
-/


-- coeilenberg comoore adjunction triangle identity 1
/-
theorem
-/


-- coeilenberg comoore adjunction triangle identity 2
/-
theorem
-/

-- defining when ? is an iso (comonadicity)
/-
def Comonadic (f : Adj) : Prop := sorry
-/
-- defining precomonadicity
/-
def Precomonadic (f : Adj) : Prop := sorry
-/

/-
structure bijunction (C : category) (D : category) where
  C : category
  D : category
  B : C ➞ D
  L : D ➞ C
  R : D ➞ C
-- counit of L ⊣ B
-- unit of L ⊣ B
-- tr 1 of L ⊣ B
-- tr 2 of L ⊣ B
-- counit of B ⊣ R
-- unit of B ⊣ R
-- tr 1 of L ⊣ B
-- tr 2 of L ⊣ B
-- comonadicity of L ⊣ B
-- monadicity of B ⊣ R
-- commutativity 
-- 
-/


structure representation where
  Obj : category
  Geo : Obj.Obj
-- Pull : bijunction Obj Bij
-- Push : bijunction Objᵒᵖ Bij
-- Id₁ : 
-- Id₂ : 
-- Ass : 
-- 
-- Hom Geo ≅ 
-- Prd Geo ≅ 
-- homotopy pullback of identity and identity is representable by the geodesic

/-
there should be an identity ⊛
[γ,-]
product with the geodesic should represent directed homotopy pushout
-/


/-
here the pullback is itself commutative
-/


/-
definition of product on objects
-/


/-
definition of product on hom
-/


/-
proof of the identity law for product
-/


/-
proof of compositionality for product
-/


/-
definition of coproduct on objects
-/


/-
definition of coproduct on hom
-/


/-
proof of the identity law for coproduct
-/


/-
proof of compositionality for coproduct
-/


-- definition of the objects of the category ⇉
/-

-/

-- definition of ℕ.Hom of the category ⇉
/-

-/


-- definition of Idn in the category ⇉
/-

-/


-- definition of Cmp in the category ⇉
/-

-/



-- proving the first identity law of the objects of the category ℕ
/-

-/

-- proving the second identity law of the objects of the category ℕ
/-

-/


-- proving associativity of the objects of the category ℕ
/-

-/



-- defining the category ⇉
def Par : category := sorry


-- notation for the category ⇉
/-
notation "⇉" => Par
-/


-- limit as an equilizer of products
/-

-/


-- colimit as an coequilizer of coproducts
/-

-/


/-
definition of equilizer on objects
-/


/-
definition of equilizer on morphisms
-/


/-
definition of the identity law for equilizer
-/


/-
definition of the compositionality law for equilizer
-/


/-
definition of the equilizer
-/


/-
definition of coequilizer on objects
-/


/-
definition of coequilizer on morphisms
-/


/-
definition of the identity law for coequilizer
-/


/-
definition of the compositionality law for coequilizer
-/


/-
definition of the coequilizer
-/


/-
definition of equilizer on objects
-/


/-
definition of equilizer on morphisms
-/


/-
definition of the identity law for equilizer
-/


/-
definition of the compositionality law for equilizer
-/


-- def equilizer


/-
definition of coequilizer on objects
-/


/-
definition of coequilizer on morphisms
-/


/-
definition of the identity law for coequilizer
-/


/-
definition of the compositionality law for coequilizer
-/


/-
definition of the coequilizer
-/


-- objects for the pullback representation in the category of categories
/-

-/


-- the pullback representation in the category of categories
/-

-/


-- the pullback representation in the category of categories
/-

-/


-- the pullback representation in the category of categories
/-

-/


-- the pullback representation in the category of categories
/-

-/


-- the pullback representation in the category of categories
/-

-/


-- the pushout representation in the opposite category of categories
/-

-/


-- definition of the objects of the category ℕ
/-

-/

-- definition of ℕ.Hom of the category ℕ
/-

-/


-- definition of Idn in the category ℕ
/-

-/


-- definition of Cmp in the category ℕ
/-

-/



-- proving the first identity law of the objects of the category ℕ
/-

-/

-- proving the second identity law of the objects of the category ℕ
/-

-/


-- proving associativity of the objects of the category ℕ
/-

-/



-- defining the category ℕ
/-

-/

