
def n : Int := 1


def reflexivity {X : Type} {x : X} : x = x := Eq.refl x


def symmetry {X : Type} {x : X} {y : X}  (p : x = y) := Eq.symm p


def transitivity {X : Type} {x : X} {y : X} {z : X} (p : x = y) (q : y = z) := Eq.trans p q


def extensionality (f g : X → Y) (p : (x:X) → f x = g x) : f = g := funext p


def equal_arguments {X : Type} {Y : Type} {a : X} {b : X} (f : X → Y) (p : a = b) : f a = f b := congrArg f p

def equal_functions {X : Type} {Y : Type} {f₁ : X → Y} {f₂ : X → Y} (p : f₁ = f₂) (x : X) : f₁ x = f₂ x := congrFun p x

def pairwise {A : Type} {B : Type} (a₁ : A) (a₂ : A) (b₁ : B) (b₂ : B) (p : a₁ = a₂) (q : b₁ = b₂) : (a₁,b₁)=(a₂,b₂) := (congr ((congrArg Prod.mk) p) q)


-- A category C consists of:
structure category.{u₀,v₀} where
  Obj : Type u₀
  Hom : Obj → Obj → Type v₀
  Idn : (X:Obj) → Hom X X
  Cmp : (X:Obj) → (Y:Obj) → (Z:Obj) → (_:Hom X Y) → (_:Hom Y Z) → Hom X Z
  Id₁ : (X:Obj) → (Y:Obj) → (f:Hom X Y) → 
    Cmp X Y Y f (Idn Y) = f
  Id₂ : (X:Obj) → (Y:Obj) → (f:Hom X Y) → 
    Cmp X X Y (Idn X) f = f
  Ass : (W:Obj) → (X:Obj) → (Y:Obj) → (Z:Obj) → (f:Hom W X) → (g:Hom X Y) → (h:Hom Y Z) →
    (Cmp W X Z) f (Cmp X Y Z g h) = Cmp W Y Z (Cmp W X Y f g) h


-- Notation for the identity map which infers the category:
def identity_map (C : category) (X : C.Obj) := C.Idn X
notation "𝟙_(" C ")" => identity_map C



-- Notation for composition which infers the category and objects:
def composition (C : category) {X : C.Obj} {Y : C.Obj} {Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) : C.Hom X Z := C.Cmp X Y Z f g
notation g "∘_(" C ")" f => composition C f g


theorem Id₁ {C : category} {X : C.Obj} { Y : C.Obj} {f : C.Hom X Y} : 
  (f ∘_(C) (𝟙_(C) X)) = f := C.Id₂ X Y f

theorem Id₂ {C : category} {X Y : C.Obj} {f : C.Hom X Y} :
  (𝟙_(C) Y ∘_(C) f) = f := C.Id₁ X Y f

theorem Ass {C : category} {W X Y Z : C.Obj} {f : C.Hom W X} {g : C.Hom X Y} {h : C.Hom Y Z} :
  ((h ∘_(C) g) ∘_(C) f) = (h ∘_(C) (g ∘_(C) f)) := (C.Ass W X Y Z f g h)


macro "cat" : tactic => `(tactic| repeat (rw [Id₁]) ; repeat (rw [Id₂]) ; repeat (rw [Ass]))
macro "CAT" : tactic => `(tactic| repeat (rw [category.Id₁]) ; repeat (rw [category.Id₂]) ; repeat (rw [category.Ass]))

example {C : category}
          {W : C.Obj} 
          {X : C.Obj}
          {Y : C.Obj}
          {Z : C.Obj}
          {f : C.Hom W X} 
          {g : C.Hom X Y} 
          {h : C.Hom Y Z}
          {i : C.Hom Z W}:
     (i ∘_(C) (h ∘_(C) (g ∘_(C) (f ∘_(C) (𝟙_(C) W))) )) 
  = ((i ∘_(C)  h) ∘_(C) ((𝟙_(C) Y) ∘_(C) g)) ∘_(C) (f) := by cat


-- obtaining a morphism from an equality
def Map (C : category) {X : C.Obj} {Y : C.Obj} (p : X = Y) : C.Hom X Y := by
subst p
exact 𝟙_(C) X


notation "Map_(" C ")" p => Map C p


-- definition of an isomorphism from X to Y
structure isomorphism (C : category) (X : C.Obj) (Y : C.Obj) where
  Fst : C.Hom X Y
  Snd : C.Hom Y X
  Id₁ : (C.Cmp X Y X Fst Snd) = C.Idn X
  Id₂ : (C.Cmp Y X Y Snd Fst) = C.Idn Y


-- notation for isomorphisms from X to Y (≅)
notation X "≅_(" C ")" Y => isomorphism C X Y


-- defining the inverse of an isomorphism between objects X and Y
def inverse {C : category} {X : C.Obj} {Y : C.Obj} (f : X ≅_(C) Y) : Y ≅_(C) X := {Fst := f.Snd, Snd := f.Fst, Id₁ := f.Id₂, Id₂ := f.Id₁}


-- notation for inverse : isos from X to Y to isos from Y to X
notation f "⁻¹" => inverse f


def SetObj := Type

def SetHom (X : SetObj) (Y : SetObj) : Type := X → Y

def SetIdn (X : SetObj) : (SetHom X X) := λ (x : X) => x  


def SetCmp (X : SetObj) (Y : SetObj) (Z : SetObj) (f : SetHom X Y) (g : SetHom Y Z) : SetHom X Z := λ (x : X) => (g (f x)) 


def SetId₁ (X : SetObj) (Y : SetObj) (f : SetHom X Y) : (SetCmp X Y Y f (SetIdn Y)) = f := funext (λ _ => rfl)

def SetId₂ (X : SetObj) (Y : SetObj) (f : SetHom X Y) : (SetCmp X X Y (SetIdn X) f) = f := rfl

def SetAss (W : SetObj) (X : SetObj) (Y : SetObj) (Z : SetObj) (f : SetHom W X) (g : SetHom X Y) (h : SetHom Y Z) : (SetCmp W X Z f (SetCmp X Y Z g h)) = (SetCmp W Y Z (SetCmp W X Y f g) h) := funext (λ _ => rfl)


def Set : category := {Obj := SetObj, Hom := SetHom, Idn := SetIdn, Cmp := SetCmp, Id₁ := SetId₁, Id₂ := SetId₂, Ass := SetAss}


-- definition of a functor
structure functor (C : category) (D : category) where
   Obj : ∀(_ : C.Obj),D.Obj
   Hom : ∀(X : C.Obj),∀(Y : C.Obj),∀(_ : C.Hom X Y),D.Hom (Obj X) (Obj Y)
   Idn : ∀(X : C.Obj),Hom X X (C.Idn X) = D.Idn (Obj X)
   Cmp : ∀(X : C.Obj),∀(Y : C.Obj),∀(Z : C.Obj),∀(f : C.Hom X Y),∀(g : C.Hom Y Z),
   D.Cmp (Obj X) (Obj Y) (Obj Z) (Hom X Y f) (Hom Y Z g) = Hom X Z (C.Cmp X Y Z f g)


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
Eq.refl (C.Idn X)

-- proving the compositionality law for the identity functor 
def CatIdnCmp (C : category) := 
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(Z : C.Obj)=>
fun(f : C.Hom X Y)=>
fun(g : C.Hom Y Z)=>
Eq.refl (C.Cmp X Y Z f g)


-- defining the identity functor
def CatIdn (C : category) : functor C C := 
{Obj := CatIdnObj C, Hom := CatIdnMor C, Idn := CatIdnIdn C, Cmp := CatIdnCmp C}


-- defining the composition G ∘_(Cat) F on objects
def CatCmpObj (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) := 
fun(X : C.Obj)=>
(G.Obj (F.Obj X))

-- defining the composition G ∘_(Cat) F on morphisms
def CatCmpHom (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) := 
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(f : C.Hom X Y)=>
(G.Hom) (F.Obj X) (F.Obj Y) (F.Hom X Y f)


-- proving the identity law for the composition G ∘_(Cat) F
def CatCmpIdn (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) := 
fun(X : C.Obj)=> 
Eq.trans (congrArg (G.Hom (F.Obj X) (F.Obj X)) (F.Idn X) ) (G.Idn (F.Obj X))


-- proving the compositionality law for the composition G ∘_(Cat) F
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
{Obj := CatCmpObj C D E F G, Hom := CatCmpHom C D E F G,Idn := CatCmpIdn C D E F G, Cmp := CatCmpCmp C D E F G}


-- proving Cat.Id₁
def CatId₁ (C : category) (D : category) (F : functor C D) : ((CatCmp C D D) F (CatIdn D) = F) := Eq.refl F

-- Proof of Cat.Id₂
def CatId₂ (C : category) (D : category) (F : functor C D) : ((CatCmp C C D) (CatIdn C) F = F) := Eq.refl F

-- Proof of Cat.Ass
def CatAss (B : category) (C : category) (D : category) (E : category) (F : functor B C) (G : functor C D) (H : functor D E) : (CatCmp B C E F (CatCmp C D E G H) = CatCmp B D E (CatCmp B C D F G) H) := 
Eq.refl (CatCmp B C E F (CatCmp C D E G H))


-- The category of categories
universe u
universe v
def Cat : category := {Obj := category.{u, v}, Hom := functor, Idn := CatIdn, Cmp := CatCmp, Id₁:= CatId₁, Id₂:= CatId₂, Ass := CatAss}


notation "𝟙" X => 𝟙_(Cat) X

notation g "∘" f => g ∘_(Cat) f 


-- The opposite category

def OppObj (C : category) := C.Obj

def OppHom (C : category) (X : OppObj C) (Y : C.Obj) := C.Hom Y X

def OppIdn (C : category) (X : OppObj C) : OppHom C X X := C.Idn X

def OppCmp (C : category) (X : OppObj C) (Y : OppObj C) (Z : OppObj C) (F : OppHom C X Y) (G : OppHom C Y Z) : OppHom C X Z := C.Cmp Z Y X G F

def OppId₁ (C : category) (X : OppObj C) (Y : OppObj C) (f : OppHom C X Y) := C.Id₂ Y X f

def OppId₂ (C : category) (X : OppObj C) (Y : OppObj C) (f : OppHom C X Y) := C.Id₁ Y X f

def OppAss (C : category) (W : OppObj C) (X : OppObj C) (Y : OppObj C) (Z : OppObj C) (f : OppHom C W X) (g : OppHom C X Y) (h : OppHom C Y Z) := Eq.symm (C.Ass Z Y X W h g f)


def Opp (C : category) : category := {Obj := OppObj C, Hom := OppHom C, Idn := OppIdn C, Cmp := OppCmp C, Id₁ := OppId₁ C, Id₂ := OppId₂ C, Ass := OppAss C}

notation C "ᵒᵖ" => Opp C


-- notation : 10000 C "̂" => (Cᵒᵖ →_Cat Set)


-- definition of the Yoneda embedding on objects
/-
def yoneda_embeddingObj (C : category) :
-/


-- definition of the Yoneda embedding on morphisms
/-
def yoneda_embeddingHom (C : category) :
-/


-- proving the identity law for the Yoneda embedding
/-
def yoneda_embeddingIdn (C : category) :
-/


-- proving the compositionality law for the Yoneda embedding
/-
def yoneda_embeddingCmp (C : category) :
-/


-- definition of the yoneda embedding
-- def yoneda_embedding (C : category) : functor C (Cᵒᵖ →_Cat Set) := sorry


-- notation for the Yoneda embedding
-- notation "よ" => yoneda_embedding


-- definition of the contravariant Yoneda embedding on objects
/-
def contravariant_yoneda_embeddingObj (C : category) :
-/


-- definition of the contravariant Yoneda embedding on morphisms
/-
def contravariant_yoneda_embeddingHom (C : category) :
-/


-- proving the identity law for the contravariant Yoneda embedding
/-
def contravariant_yoneda_embeddingIdn (C : category) :
-/


-- proving the compositionality law for the contravariant Yoneda embedding
/-
def contravariant_yoneda_embeddingCmp (C : category) :
-/


-- definition of the contravariant yoneda embedding
-- def contravariant_yoneda_embedding (C : category) : functor (Cᵒᵖ) (C →_Cat Set) := sorry


-- notation for the contravariant yoneda embedding
-- notation "よᵒᵖ" => contravariant_yoneda_embedding


-- def the_yoneda_lemma (C : category) (X: C.Obj) (F : (Cᵒᵖ →_Cat Set).Obj) : ((Cᵒᵖ →_Cat Set).Hom ((よ C).Obj X) F) ≅_(Set)  F.Obj X := sorry


-- def the_contravariant_yoneda_lemma (C : category) (X: Cᵒᵖ.Obj) (F : (C →_Cat Set).Obj) : ((C →_Cat Set).Hom ((よᵒᵖ C).Obj X) F) ≅_(Set)  F.Obj X := sorry


-- theorem the_yoneda_embedding_is_fully_faithful : (Cᵒᵖ →_Cat Set).Hom ((よ C).Obj X) ((よ C).Obj Y) ≅_(Set) C.Hom X Y := sorry


-- theorem the_contravariant_yoneda_embedding_is_fully_faithful : (C →_Cat Set).Hom ((よᵒᵖ C).Obj X) ((よᵒᵖ C).Obj Y) ≅_(Set) Cᵒᵖ.Hom X Y := sorry


-- defining the objects of the CatPrd C D
def CatPrdObj (C : category) (D : category) := (D.Obj) × (C.Obj)

-- defining the morphisms of CatPrd C D
def CatPrdHom (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) := (D.Hom X.1 Y.1) × (C.Hom X.2 Y.2)

-- defining the identity functor on an object in C × D
def CatPrdIdn (C : category) (D : category) (X : CatPrdObj C D) := ((D.Idn X.1),(C.Idn X.2))

-- defining the composition on morphisms in C × D
def CatPrdCmp (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (Z : CatPrdObj C D) (f : CatPrdHom C D X Y) (g : CatPrdHom C D Y Z) : CatPrdHom C D X Z := (D.Cmp X.1 Y.1 Z.1 f.1 g.1, C.Cmp X.2 Y.2 Z.2 f.2 g.2)


-- proving the first identity law for morphisms in C ×_Cat D 
theorem CatPrdId₁ (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (f : CatPrdHom C D X Y) :
  CatPrdCmp C D X Y Y f (CatPrdIdn C D Y) = f :=  by
  unfold CatPrdCmp
  unfold CatPrdIdn
  cases f
  rw [category.Id₁]
  rw [category.Id₁]

-- proving the second identity law for morphisms in C ×_Cat D 
theorem CatPrdId₂ (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (f : CatPrdHom C D X Y) : CatPrdCmp C D X X Y (CatPrdIdn C D X) f = f := by
  unfold CatPrdCmp
  unfold CatPrdIdn
  cases f
  rw [category.Id₂]
  rw [category.Id₂]

-- proving associativity for morphisms in C ×_Cat D
theorem CatPrdAss 
  (C : category) (D : category)
  (W : CatPrdObj C D) (X : CatPrdObj C D) 
  (Y : CatPrdObj C D) (Z : CatPrdObj C D)
  (f : CatPrdHom C D W X) (g : CatPrdHom C D X Y) (h : CatPrdHom C D Y Z) :
  CatPrdCmp C D W X Z f (CatPrdCmp C D X Y Z g h) = CatPrdCmp C D W Y Z (CatPrdCmp C D W X Y f g) h := by
  unfold CatPrdCmp
  rw [category.Ass]
  rw [category.Ass]


-- defining the CatPrd of two categories
def CatPrd (C : category) (D : category) : category := {Obj := CatPrdObj C D, Hom := CatPrdHom C D, Idn := CatPrdIdn C D, Cmp := CatPrdCmp C D, Id₁ := CatPrdId₁ C D, Id₂:= CatPrdId₂ C D, Ass := CatPrdAss C D}


notation:1000  D "×_Cat" C => CatPrd C D


def FunPrdObj 
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂) 
  (X : (C₁ ×_Cat C₂).Obj): 
  (D₁ ×_Cat D₂).Obj := 
  (F.Obj X.fst, G.Obj X.snd)


def FunPrdHom 
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂) 
  (X : (C₁ ×_Cat C₂).Obj)
  (Y : (C₁ ×_Cat C₂).Obj) 
  (f : (C₁ ×_Cat C₂).Hom X Y) :
  ((D₁ ×_Cat D₂).Hom (FunPrdObj F G X) (FunPrdObj F G Y) ) := 
  (F.Hom X.fst Y.fst f.fst, G.Hom X.snd Y.snd f.snd)


def FunPrdIdn 
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂)
  (X : (C₁ ×_Cat C₂).Obj) :
  (FunPrdHom F G X X ((C₁ ×_Cat C₂).Idn X))  = ((D₁ ×_Cat D₂).Idn (FunPrdObj F G X)) :=   by
  unfold FunPrdHom
  unfold FunPrdObj
  cases X
  simp
  sorry


def FunPrdCmp 
  {C₁ : category} 
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂) 
  (X : (C₁ ×_Cat C₂).Obj)
  (Y : (C₁ ×_Cat C₂).Obj)
  (Z : (C₁ ×_Cat C₂).Obj)
  (f : (C₁ ×_Cat C₂).Hom X Y)
  (g : (C₁ ×_Cat C₂).Hom Y Z) :
  ((D₁ ×_Cat D₂).Cmp (FunPrdObj F G X) (FunPrdObj F G Y) (FunPrdObj F G Z) ((FunPrdHom F G) X Y f) (FunPrdHom F G Y Z g)) = (FunPrdHom F G X Z ((C₁ ×_Cat C₂).Cmp X Y Z f g)) := by
  unfold FunPrdHom
  cases X
  cases Y
  cases Z
  simp
  rw [functor.Hom]
  sorry


def FunPrd 
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂) : 
  Cat.Hom (C₁ ×_Cat C₂) (D₁ ×_Cat D₂) := 
  {Obj := FunPrdObj F G, Hom := FunPrdHom F G, Idn := FunPrdIdn F G, Cmp := FunPrdCmp F G}


notation F "×_Fun" G => FunPrd F G


-- defining the category *_Cat
def PntObj : Type := Unit
def PntHom (_ : PntObj) (_ : PntObj) : Type := Unit
def PntIdn (X : PntObj) : PntHom X X := Unit.unit
def PntCmp (X : PntObj) (Y : PntObj) (Z : PntObj) (_ : PntHom X Y) (_ : PntHom Y Z) : PntHom X Z := Unit.unit
def PntId₁ (X : PntObj) (Y : PntObj) (f : PntHom X Y) : PntCmp X Y Y f (PntIdn Y) = f := Eq.refl f
def PntId₂ (X : PntObj) (Y : PntObj) (f : PntHom X Y) : PntCmp X X Y (PntIdn X) f = f := Eq.refl f
def PntAss (W : PntObj) (X : PntObj) (Y : PntObj) (Z : PntObj) (f : PntHom W X) (g : PntHom X Y) (h : PntHom Y Z) : PntCmp W Y Z (PntCmp W X Y f g) h = PntCmp W X Z f (PntCmp X Y Z g h) := Eq.refl Unit.unit
def Pnt : category := {Obj := PntObj, Hom := PntHom, Idn := PntIdn, Cmp := PntCmp, Id₁ := PntId₁, Id₂ := PntId₂, Ass := PntAss}


-- notation for the category *_Cat
notation "*_Cat" => Pnt
notation "*_(Cat)" => Pnt



def PrdId₁Fst (C : category) : Cat.Hom C (C ×_Cat *_Cat) := sorry

def PrdId₁Snd (C : category) : Cat.Hom (C ×_Cat *_Cat) C := sorry


def PrdId₁Id₁ (C : category) : ((PrdId₁Snd C) ∘_(Cat) (PrdId₁Fst C)) = 𝟙_(Cat) C := sorry

def PrdId₁Id₂ (C : category) : ((PrdId₁Fst C) ∘_(Cat) (PrdId₁Snd C)) = 𝟙_(Cat) (C ×_Cat *_Cat) := sorry


def PrdId₁ (C : category) :  C ≅_(Cat) (C ×_Cat *_Cat)  := {Fst := PrdId₁Fst C, Snd:= PrdId₁Snd C, Id₁ := PrdId₁Id₁ C, Id₂ := PrdId₁Id₂ C}


def PrdId₂Fst (C : category) : Cat.Hom C (*_Cat ×_Cat C) := sorry

def PrdId₂Snd (C : category) : Cat.Hom (*_Cat ×_Cat C) C := sorry


def PrdId₂Id₁ (C : category) : ((PrdId₂Snd C) ∘_(Cat) (PrdId₂Fst C)) = 𝟙_(Cat) C := sorry

def PrdId₂Id₂ (C : category) : ((PrdId₂Fst C) ∘_(Cat) (PrdId₂Snd C)) = 𝟙_(Cat) (*_Cat ×_Cat C) := sorry


def PrdId₂ (C : category) :  C ≅_(Cat) (*_Cat ×_Cat C)  := {Fst := PrdId₂Fst C, Snd:= PrdId₂Snd C, Id₁ := PrdId₂Id₁ C, Id₂ := PrdId₂Id₂ C}


def PrdAssFst
  (C : category) 
  (D : category) 
  (E : category) : 
  Cat.Hom (C ×_Cat D ×_Cat E) ((C ×_Cat D) ×_Cat E) := sorry

def PrdAssSnd
  (C : category) 
  (D : category) 
  (E : category) : 
  Cat.Hom ((C ×_Cat D) ×_Cat E) (C ×_Cat D ×_Cat E) := sorry


def PrdAssId₁
  (C : category) 
  (D : category) 
  (E : category) : ((PrdAssSnd C D E) ∘_(Cat) (PrdAssFst C D E)) = 𝟙_(Cat) (C ×_Cat D ×_Cat E) := sorry

def PrdAssId₂
  (C : category) 
  (D : category) 
  (E : category) :  ((PrdAssFst C D E) ∘_(Cat) (PrdAssSnd C D E)) = 𝟙_(Cat) ((C ×_Cat D) ×_Cat E)  := sorry


def PrdAss
  (C : category) 
  (D : category) 
  (E : category) : (C ×_Cat D ×_Cat E)≅_(Cat) ((C ×_Cat D) ×_Cat E)    := {Fst := PrdAssFst C D E, Snd:= PrdAssSnd C D E, Id₁ := PrdAssId₁ C D E, Id₂ := PrdAssId₂ C D E}


-- definition of a (strict) twocategory
structure twocategory.{w} where
  Obj : Type w
  Hom : Obj → 
        Obj → 
        category
  Idn : (C : Obj) → 
        Cat.Hom *_Cat (Hom C C)
  Cmp : (C : Obj) → 
        (D : Obj) → 
        (E : Obj) → 
        Cat.Hom ((Hom C D) ×_Cat (Hom D E)) (Hom C E)
  Id₁ : (C : Obj) →
        (D : Obj) →
        ((Cmp C D D) ∘_(Cat) ((𝟙_(Cat) (Hom C D)) ×_Fun (Idn D)) ∘_(Cat) (PrdId₁ (Hom C D)).Fst) = (𝟙_(Cat) (Hom C D))
  Id₂ : (C : Obj) →
        (D : Obj) →
        ((Cmp C C D) ∘_(Cat) ((Idn C) ×_Fun (𝟙_(Cat) (Hom C D))) ∘_(Cat) (PrdId₂Fst (Hom C D))) = (𝟙_(Cat) (Hom C D))     
  Ass : (B : Obj) →
        (C : Obj) →
        (D : Obj) →
        (E : Obj) →
        ((Cmp B C E) ∘_(Cat) ((𝟙_(Cat) (Hom B C)) ×_Fun (Cmp C D E))) = (Cmp B D E) ∘_(Cat) ((Cmp B C D) ×_Fun (𝟙_(Cat) (Hom D E))) ∘_(Cat) (PrdAss (Hom B C) (Hom C D) (Hom D E)).Fst


-- definition of a twofunctor
structure twofunctor (C : twocategory) (D : twocategory) where
  Obj : C.Obj → D.Obj
  Hom : (X : C.Obj) → (Y : C.Obj) → (functor (C.Hom X Y) (D.Hom (Obj X) (Obj Y)))
-- Idn : (X : C.Obj) → ≅_(???)
-- Cmp : (X : C.Obj) → (Y : C.Obj) → (Z : C.Obj) → ≅_(???)


-- defining the identity component of the category TwoCat
def TwoCatIdn (C : twocategory) : (twofunctor C C) := sorry


-- defining the composition component of the category TwoCat
def TwoCatCmp (C : twocategory) (D : twocategory) (E : twocategory) (F : twofunctor C D) (G : twofunctor D E) : twofunctor C E := sorry


-- defining the first identity component of the category TwoCat
def TwoCatId₁ (C : twocategory) (D : twocategory) (F : twofunctor C D) : (TwoCatCmp C D D F (TwoCatIdn D)) = F := sorry


-- defining the second identity component of the category TwoCat
def TwoCatId₂ (C : twocategory) (D : twocategory) (F : twofunctor C D) : (TwoCatCmp C C D (TwoCatIdn C) F) = F := sorry


-- defining the associativity component of the category TwoCat
def TwoCatAss (B : twocategory) (C : twocategory) (D : twocategory) (E : twocategory) (F : twofunctor B C) (G : twofunctor C D) (H : twofunctor D E) : TwoCatCmp B D E (TwoCatCmp B C D F G) H = TwoCatCmp B C E F (TwoCatCmp C D E G H) := sorry


-- Assembling the category TwoCat
def TwoCat : category := {Obj := twocategory, Hom := twofunctor, Idn := TwoCatIdn, Cmp := TwoCatCmp, Id₁ := TwoCatId₁, Id₂ := TwoCatId₂, Ass := TwoCatAss}


-- Notation for the identity map which infers the category:
def twocategory_identity (C : twocategory) (X : C.Obj) : (C.Hom X X).Obj := ((C.Idn X).Obj Unit.unit)
notation "𝟏_(" C ")" => twocategory_identity C


-- Notation for composition in a twocategory which infers the category and objects:

def composition_on_objects (C : twocategory) {X : C.Obj} {Y : C.Obj} {Z : C.Obj} (f : (C.Hom X Y).Obj) (g : (C.Hom Y Z).Obj) : (C.Hom X Z).Obj := (C.Cmp X Y Z).Obj (f, g)
notation: 1000 g "•_(" C ")" f => composition_on_objects C f g

def TwoCmpObj {C : twocategory} {X : C.Obj} {Y : C.Obj} {Z : C.Obj} (f : (C.Hom X Y).Obj) (g : (C.Hom Y Z).Obj) : (C.Hom X Z).Obj :=  (C.Cmp X Y Z).Obj (f, g)
notation: 1000 g "•" f => TwoCmpObj f g


def composition_on_morphisms (C : twocategory) {X : C.Obj} {Y : C.Obj} {Z : C.Obj} {F₁ : (C.Hom X Y).Obj} {F₂ : (C.Hom X Y).Obj} {G₁ : (C.Hom Y Z).Obj} {G₂ : (C.Hom Y Z).Obj} (η : (C.Hom X Y).Hom F₁ F₂) (ε : (C.Hom Y Z).Hom G₁ G₂) : (C.Hom X Z).Hom (G₁ • F₁) (G₂ • F₂) := (C.Cmp X Y Z).Hom (F₁,G₁) (F₂,G₂) (η,ε)
notation: 1000 g "∙_(" C ")" f => composition_on_morphisms C f g

def TwoCmpHom {C : twocategory} {X : C.Obj} {Y : C.Obj} {Z : C.Obj} {F₁ : (C.Hom X Y).Obj} {F₂ : (C.Hom X Y).Obj} {G₁ : (C.Hom Y Z).Obj} {G₂ : (C.Hom Y Z).Obj} (η : (C.Hom X Y).Hom F₁ F₂) (ε : (C.Hom Y Z).Hom G₁ G₂) : (C.Hom X Z).Hom (G₁ • F₁) (G₂ • F₂) := (C.Cmp X Y Z).Hom (F₁,G₁) (F₂,G₂) (η,ε)
notation : 1000 g "∙" f => TwoCmpHom f g


/-
theorem Id₁Obj {C : category} {X : C.Obj} {Y : C.Obj} {f : C.Hom X Y} : 
  (f ∘_(C) (𝟙_(C) X)) = f := C.Id₂ X Y f

theorem Id₁Hom {C : category} {X : C.Obj} {Y : C.Obj} {f : C.Hom X Y} : 
  (f ∘_(C) (𝟙_(C) X)) = f := C.Id₂ X Y f

theorem Id₂Obj {C : category} {X Y : C.Obj} {f : C.Hom X Y} :
  (𝟙_(C) Y ∘_(C) f) = f := C.Id₁ X Y f

theorem Id₂Hom {C : category} {X Y : C.Obj} {f : C.Hom X Y} :
  (𝟙_(C) Y ∘_(C) f) = f := C.Id₁ X Y f

theorem AssObj {C : category} {W X Y Z : C.Obj} {f : C.Hom W X} {g : C.Hom X Y} {h : C.Hom Y Z} :
  ((h ∘_(C) g) ∘_(C) f) = (h ∘_(C) (g ∘_(C) f)) := (C.Ass W X Y Z f g h)

theorem AssHom {C : category} {W X Y Z : C.Obj} {f : C.Hom W X} {g : C.Hom X Y} {h : C.Hom Y Z} :
  ((h ∘_(C) g) ∘_(C) f) = (h ∘_(C) (g ∘_(C) f)) := (C.Ass W X Y Z f g h)
-/


-- def interchange_law (T : twocategory) (C : T.Obj) (D : T.Obj) (E : T.Obj) ( : : (T.Cmp C D E).Hom ((Hom C D) ×_Cat (Hom D E)) (Hom C E) := T.Cmp.Hom


/-
macro "twocat" : tactic => `(tactic| repeat (rw [Id₁Obj]) ; repeat (rw [Id₁Hom]) ; repeat (rw [Id₂Obj]) ; repeat (rw [Id₂Hom]); repeat (rw [AssObj])) ; repeat (rw [AssHom]))

-- example of the cat tactic
example {C : category}
          {W : C.Obj} 
          {X : C.Obj}
          {Y : C.Obj}
          {Z : C.Obj}
          {A : C.Obj}
          {f : C.Hom W X} 
          {g : C.Hom X Y} 
          {h : C.Hom Y Z}
          {i : C.Hom Z A}: 
     (i ∘_(C) (h ∘_(C) (g ∘_(C) (f ∘_(C) (𝟙_(C) W))) )) 
  = ((i ∘_(C)  h) ∘_(C) ((𝟙_(C) Y) ∘_(C) g)) ∘_(C) (f) := by cat
-/


-- obtaining a morphism from an equality
def TwoMap (C : twocategory) {X : C.Obj} {Y : C.Obj} (p : X = Y) : (C.Hom X Y).Obj := by
subst p
exact 𝟏_(C) X


notation "TwoMap_(" C ")" p => TwoMap C p


-- definition of an equivalence from X to Y
structure equivalence (T : twocategory) (X : T.Obj) (Y : T.Obj) where
  Fst : (T.Hom X Y).Obj
  Snd : (T.Hom Y X).Obj
  Id₁ : (T.Cmp X Y X).Obj (Fst,Snd) ≅_(T.Hom X X) (𝟏_(T) X)
  Id₂ : (T.Cmp Y X Y).Obj (Snd,Fst) ≅_(T.Hom Y Y) (𝟏_(T) Y)


-- notation for equivalences from C to D (≃)
notation C "≃_(" T ")" D => equivalence T C D


-- defining the inverse of an isomorphism between objects X and Y
def twocategory_inverse {T : twocategory} {C : T.Obj} {D : T.Obj} (f : C ≃_(T) D) : D ≃_(T) C := sorry -- {Fst := f.Snd, Snd := f.Fst, Id₁ := f.Id₂, Id₂ := f.Id₁}


-- notation for inverse of an equivalence : isos from X to Y to isos from Y to X
-- notation f "⁻¹" => inverse f


def is_equivalence (T : twocategory) {C : T.Obj} {D : T.Obj} (F : (T.Hom C D).Obj) : Prop := ∃(G : (T.Hom D C).Obj),∃(_ : (T.Cmp C D C).Obj (F,G) ≅_(T.Hom C C) (𝟏_(T) C)),∃(_ : (T.Cmp D C D).Obj (G,F) ≅_(T.Hom D D) (𝟏_(T) D)),True


universe u₂
universe v₂ 


-- defining natural transformations for a category C and a category D
structure HomHom (C : category) (D : category) (F : functor C D) (G : functor C D) where
  Obj : (X : C.Obj) → (D.Hom (F.Obj X) (G.Obj X))
  Nat : (X : C.Obj) → (Y : C.Obj) → (f : C.Hom X Y) → (D.Cmp (F.Obj X) (F.Obj Y) (G.Obj Y) (F.Hom X Y f) (Obj Y)) = (D.Cmp (F.Obj X) (G.Obj X) (G.Obj Y) (Obj X) (G.Hom X Y f))


-- notation for natural transformations
def natural_transformation {C : category} {D : category} (F : functor C D) (G : functor C D) := HomHom C D F G


-- defining the identity natural transformation of a functor
def HomIdnObj (C : category) (D : category) (F : functor C D) (X : C.Obj) : (D.Hom (F.Obj X) (F.Obj X)) := D.Idn (F.Obj X)


-- helping to prove the naturality of the identity functor
def HomIdnNat₁ (C : category) (D : category) (F : functor C D) (X : C.Obj) (Y : C.Obj) (f : C.Hom X Y) : (D.Cmp (F.Obj X) (F.Obj Y) (F.Obj Y) (F.Hom X Y f) (HomIdnObj C D F Y)) = F.Hom X Y f := D.Id₁ (functor.Obj F X) (functor.Obj F Y) (functor.Hom F X Y f)

-- starting to prove the naturality of the identity functor
def HomIdnNat₂ (C : category) (D : category) (F : functor C D) (X : C.Obj) (Y : C.Obj) (f : C.Hom X Y) : (D.Cmp (F.Obj X) (F.Obj X) (F.Obj Y) (HomIdnObj C D F X) (F.Hom X Y f)) = F.Hom X Y f := D.Id₂ (functor.Obj F X) (functor.Obj F Y) (functor.Hom F X Y f)

-- proving the naturality of the identity functor, (C →_Cat D).Idn.Nat
def HomIdnNat (C : category) (D : category) (F : functor C D) (X : C.Obj) (Y : C.Obj) (f : C.Hom X Y) : (D.Cmp (F.Obj X) (F.Obj Y) (F.Obj Y) (F.Hom X Y f) (HomIdnObj C D F Y)) = (D.Cmp (F.Obj X) (F.Obj X) (F.Obj Y) (HomIdnObj C D F X) (F.Hom X Y f)) := Eq.trans (HomIdnNat₁ C D F X Y f) (Eq.symm (HomIdnNat₂ C D F X Y f))


-- defining (C →_Cat D).Idn for a category C and a category D
def HomIdn (C : category) (D : category) (F : Cat.Hom C D) : HomHom C D F F := {Obj := HomIdnObj C D F, Nat := HomIdnNat C D F}


-- defining composition of natural transformations
def HomCmpObj (C : category) (D : category) (F : functor C D) (G : functor C D) (H : functor C D) (f : HomHom C D F G) (g : HomHom C D G H) (X : C.Obj) :  D.Hom (F.Obj X) (H.Obj X) := (g.Obj X) ∘_(D) (f.Obj X)

-- defining composition of natural transformations
def HomCmpNat (C : category) (D : category) (F : functor C D) (G : functor C D) (H : functor C D) (f : HomHom C D F G) (g : HomHom C D G H) (X : C.Obj) (Y : C.Obj) (α : C.Hom X Y) : (((g.Obj Y) ∘_(D) (f.Obj Y)) ∘_(D) (F.Hom X Y α))  = ((H.Hom X Y α) ∘_(D) ((g.Obj X) ∘_(D) (f.Obj X)))  := sorry

-- defining composition of natural transformations
def HomCmp (C : category) (D : category) (F : functor C D) (G : functor C D) (H : functor C D) (f : HomHom C D F G) (g : HomHom C D G H) : HomHom C D F H := {Obj := HomCmpObj C D F G H f g, Nat := HomCmpNat C D F G H f g}


-- proving the identity laws and associativity for the category C →_Cat D

-- proving the first identity law of the functor category C →_Cat D
def HomId₁ (C : category) (D : category) (F : functor C D) (G : functor C D) (f : HomHom C D F G) : HomCmp C D F G G f (HomIdn C D G) = f := sorry

-- proving the second identity law of the functor category C →_Cat D
def HomId₂ (C : category) (D : category) (F : functor C D) (G : functor C D) (f : HomHom C D F G) : HomCmp C D F F G (HomIdn C D F) f = f := sorry

-- proving associativity of the functor category C →_Cat D
def HomAss (C : category) (D : category) (F : functor C D) (G : functor C D) (H : functor C D) (I : functor C D) (α : HomHom C D F G) (β : HomHom C D G H) (γ : HomHom C D H I) : (HomCmp C D F G I α (HomCmp C D G H I β γ)) = (HomCmp C D F H I (HomCmp C D F G H α β) γ) := sorry


-- defining the category C →_Cat D for a category C and a category D
def ℂ𝕒𝕥Hom (C : Cat.Obj) (D : Cat.Obj) : Cat.Obj := {Obj := functor C D, Hom := HomHom C D, Idn := HomIdn C D, Cmp := HomCmp C D, Id₁ := HomId₁ C D, Id₂ := HomId₂ C D, Ass := HomAss C D}


-- defining 𝐂𝐚𝐭.Idn.Obj
def ℂ𝕒𝕥IdnObj (C : category) (_ : Unit) := Cat.Idn C


-- defining the functor categories.Idn.Hom on morphisms
def ℂ𝕒𝕥IdnHom (C : category) (_: Unit) (_: Unit) (_: Unit) := (ℂ𝕒𝕥Hom C C).Idn (Cat.Idn C)


-- proving the identity law for the functor categories.TwoIdn
def ℂ𝕒𝕥IdnIdn (C : category) (X : Unit) : ℂ𝕒𝕥IdnHom C X X ((*_Cat).Idn X) = (ℂ𝕒𝕥Hom C C).Idn (ℂ𝕒𝕥IdnObj C X) := sorry


-- proving compositionality for the functor categories.TwoIdn
def ℂ𝕒𝕥IdnCmp (C : category) (X : Unit) (Y : Unit) (Z : Unit) (f: (*_Cat).Hom X Y) (g: (*_Cat).Hom Y Z) : ( (ℂ𝕒𝕥Hom C C).Cmp (ℂ𝕒𝕥IdnObj C X) (ℂ𝕒𝕥IdnObj C Y) (ℂ𝕒𝕥IdnObj C Z) (ℂ𝕒𝕥IdnHom C X Y f) (ℂ𝕒𝕥IdnHom C Y Z g) ) = (ℂ𝕒𝕥IdnHom C X Z ((*_Cat).Cmp X Y Z f g)) := sorry


-- def 𝐂𝐚𝐭.Idn
def ℂ𝕒𝕥Idn (C : category) : Cat.Hom *_Cat (ℂ𝕒𝕥Hom C C) := {Obj := ℂ𝕒𝕥IdnObj C, Hom := ℂ𝕒𝕥IdnHom C, Idn := ℂ𝕒𝕥IdnIdn C, Cmp := ℂ𝕒𝕥IdnCmp C}


-- defining 𝐂𝐚𝐭.Cmp.Obj
def ℂ𝕒𝕥CmpObj (C : category) (D : category) (E : category) : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Obj → (ℂ𝕒𝕥Hom C E).Obj := sorry


--  defining 𝐂𝐚𝐭.Cmp.Hom
def ℂ𝕒𝕥CmpHom (C : category) (D : category) (E : category) (X : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Obj) (Y : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Obj) (P : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Hom X Y) : ((ℂ𝕒𝕥Hom C E).Hom (ℂ𝕒𝕥CmpObj C D E X) (ℂ𝕒𝕥CmpObj C D E Y) ) := sorry


-- defining the horizontal composition of natural transformations
-- def horizontal_composition {C : category} {D : category} {E : category} {F₁ : (ℂ𝕒𝕥Hom C D).Obj} {F₂ : (ℂ𝕒𝕥Hom C D).Obj} {G₁ : (ℂ𝕒𝕥Hom D E).Obj} {G₂ : (ℂ𝕒𝕥Hom D E).Obj} (f : (ℂ𝕒𝕥Hom C D).Hom F₁ F₂) (g : (ℂ𝕒𝕥Hom D E).Hom G₁ G₂) := sorry


-- notation for the horizontal composition of natural transformations
-- notation f "∙" g => horizontal_composition g f


-- proving the identity law equation for 𝐂𝐚𝐭.Cmp
def ℂ𝕒𝕥CmpIdn (C : category) (D : category) (E : category) (X : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Obj) : ℂ𝕒𝕥CmpHom C D E X X (((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Idn X) = ((ℂ𝕒𝕥Hom C E).Idn (ℂ𝕒𝕥CmpObj C D E X)) := sorry


-- proving compositionality for the functor 𝐂𝐚𝐭.Cmp
def ℂ𝕒𝕥CmpCmp (C : category) (D : category) (E : category) (X : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Obj) (Y : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Obj) (Z : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Obj) (P : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Hom X Y) (Q : ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Hom Y Z) : 
((ℂ𝕒𝕥Hom C E).Cmp 
  (ℂ𝕒𝕥CmpObj C D E X) 
  (ℂ𝕒𝕥CmpObj C D E Y) 
  (ℂ𝕒𝕥CmpObj C D E Z) 
  (ℂ𝕒𝕥CmpHom C D E X Y P) 
  (ℂ𝕒𝕥CmpHom C D E Y Z Q)) = 
  (ℂ𝕒𝕥CmpHom C D E X Z 
  (((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)).Cmp X Y Z P Q)) := sorry


--  categories.Cmp : (C : Obj) → (D : Obj) → (E : Obj) → (Hom C D) × (Hom D E) → (Hom C E)    
def ℂ𝕒𝕥Cmp (C : category) (D : category) (E : category) : functor ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)) (ℂ𝕒𝕥Hom C E) := {Obj := ℂ𝕒𝕥CmpObj C D E, Hom := ℂ𝕒𝕥CmpHom C D E, Idn := ℂ𝕒𝕥CmpIdn C D E, Cmp := ℂ𝕒𝕥CmpCmp C D E}


--  Id₁ : (C : Obj) → (D : Obj) → (Cats.Id₁)
/-
def Id₁ : (C : category) → (D : category) → (F : functor C D) → 
-/

def ℂ𝕒𝕥Id₁ :  ∀ (C D : Cat.Obj),
  ((ℂ𝕒𝕥Cmp C D D)∘_(Cat)(𝟙_(Cat) (ℂ𝕒𝕥Hom C D) ×_Fun ℂ𝕒𝕥Idn D)∘_(Cat)(PrdId₁ (ℂ𝕒𝕥Hom C D)).Fst) =
  𝟙_(Cat) (ℂ𝕒𝕥Hom C D) := sorry




--  
def ℂ𝕒𝕥Id₂ : (C : Cat.Obj) →
        (D : Cat.Obj) →
        ((ℂ𝕒𝕥Cmp C C D) ∘_(Cat) ((ℂ𝕒𝕥Idn C) ×_Fun (𝟙_(Cat) (ℂ𝕒𝕥Hom C D))) ∘_(Cat) (PrdId₂Fst (ℂ𝕒𝕥Hom C D))) = (𝟙_(Cat) (ℂ𝕒𝕥Hom C D))  := sorry


-- proving associativity of composition for the twocategory of categories
def ℂ𝕒𝕥Ass : (B : Cat.Obj) →
          (C : Cat.Obj) →
          (D : Cat.Obj) →
          (E : Cat.Obj) →
          ((ℂ𝕒𝕥Cmp B C E) ∘_(Cat) ((𝟙_(Cat) (ℂ𝕒𝕥Hom B C)) ×_Fun (ℂ𝕒𝕥Cmp C D E))) = (ℂ𝕒𝕥Cmp B D E) ∘_(Cat) ((ℂ𝕒𝕥Cmp B C D) ×_Fun (𝟙_(Cat) (ℂ𝕒𝕥Hom D E))) ∘_(Cat) (PrdAss (ℂ𝕒𝕥Hom B C) (ℂ𝕒𝕥Hom C D) (ℂ𝕒𝕥Hom D E)).Fst := sorry



-- twocategory_of_categories 
def ℂ𝕒𝕥 : twocategory := {Obj:= Cat.Obj, Hom := ℂ𝕒𝕥Hom, Idn := ℂ𝕒𝕥Idn, Cmp := ℂ𝕒𝕥Cmp, Id₁ := ℂ𝕒𝕥Id₁, Id₂ := ℂ𝕒𝕥Id₂, Ass := ℂ𝕒𝕥Ass}


notation "𝐂𝐚𝐭" => ℂ𝕒𝕥

notation C "≃" D => equivalence 𝐂𝐚𝐭 C D


notation "𝟏" X => 𝟏_(𝐂𝐚𝐭) X


def Fun (C : 𝐂𝐚𝐭.Obj) (D : 𝐂𝐚𝐭.Obj) := (𝐂𝐚𝐭.Hom C D).Obj


notation : 1000 C "⭢" D => Fun C D


def essentially_surjective {C : 𝐂𝐚𝐭.Obj} {D : 𝐂𝐚𝐭.Obj} (F : C ⭢ D) : Prop := sorry


def fully_faithful {C : 𝐂𝐚𝐭.Obj} {D : 𝐂𝐚𝐭.Obj} (F : C ⭢ D) : Prop := sorry


-- is_equivalence if and only if essentially surjective
-- theorem equivalences_in_𝐂𝐚𝐭 {C : 𝐂𝐚𝐭.Obj} {D : 𝐂𝐚𝐭.Obj} (F : C ⭢ D) : (is_equivalence 𝐂𝐚𝐭 F) ↔ ((fully_faithful F) ∧ (essentially_surjective F)) := sorry


-- definition of the right triangle identity
def AdjId₁ (T : twocategory) (Dom : T.Obj) (Cod : T.Obj) (Fst : (T.Hom Dom Cod).Obj) (Snd : (T.Hom Cod Dom).Obj) (η : (T.Hom Dom Dom).Hom (𝟏_(T) Dom) (Snd •_(T) Fst)) (ε: (T.Hom Cod Cod).Hom (Fst •_(T) Snd) (𝟏_(T) Cod)) : Prop := sorry


-- definition of the left triangle identity
def AdjId₂ (T : twocategory) (Dom : T.Obj) (Cod : T.Obj) (Fst : (T.Hom Dom Cod).Obj) (Snd : (T.Hom Cod Dom).Obj) (η : (T.Hom Dom Dom).Hom (𝟏_(T) Dom) (Snd •_(T) Fst)) (ε: (T.Hom Cod Cod).Hom (Fst •_(T) Snd) (𝟏_(T) Cod)) : Prop := sorry


-- definition of an adjunction

structure adjunction (T : twocategory) where
  Dom : T.Obj
  Cod : T.Obj
  Fst : (T.Hom Dom Cod).Obj
  Snd : (T.Hom Cod Dom).Obj
  η : (T.Hom Dom Dom).Hom (𝟏_(T) Dom) (Snd •_(T) Fst)
  ε : (T.Hom Cod Cod).Hom (Fst •_(T) Snd) (𝟏_(T) Cod)
  Id₁ : AdjId₁ T Dom Cod Fst Snd η ε
  Id₂ : AdjId₂ T Dom Cod Fst Snd η ε


def left_adjoint {C : twocategory} (f : adjunction C) : (C.Hom f.Dom f.Cod).Obj := f.Fst


notation f "𛲔" => left_adjoint f


def right_adjoint {C : twocategory} (f : adjunction C) : (C.Hom f.Cod f.Dom).Obj := f.Snd


notation f "ॱ" => right_adjoint f


def is_adjoint {T : twocategory} {C : T.Obj} {D : T.Obj} (F : (T.Hom C D).Obj) (G : (T.Hom D C).Obj) : Prop := sorry --  ∃ (f : Adj T), ((f.Fst = F)∧(f.Snd = G))

notation F "⊣" G => is_adjoint F G


def is_left_adjoint {C : category} {D : category} (F : Cat.Hom C D) : Prop := sorry --  ∃ (f : Adj T),(f.Fst = F)

notation F "⊣" "-" => is_left_adjoint F


def is_right_adjoint {C : category} {D : category} (G : Cat.Hom D C) : Prop := sorry --  ∃ (f : Adj T), (f.Snd = G)

notation "-" "⊣" G => is_right_adjoint G


-- currying a 1-morphism one way
/-
def curryFst : := sorry
-/


-- currying a 1-morphism one way
/-
def currySnd : := sorry
-/


-- currying Id₁
/-
def curryId₁ : := sorry
-/


-- currying Id₂
/-
def curryId₂ : := sorry
-/


-- the currying isomorphism
def curry (C : category) (D : category) (F : (𝐂𝐚𝐭.Hom C D).Obj) (G : (𝐂𝐚𝐭.Hom D C).Obj) (X : C.Obj) (Y : D.Obj) : (C.Hom X (G.Obj Y)) ≅_(Set) (D.Hom (F.Obj X) Y) := sorry


-- uniqueness of left adjoints up to natural isomorphism
/-

-/


-- uniqueness of right adjoints up to natural isomorphism
/-

-/


-- the first identity law for a monad
def MonId₁ (T : twocategory) (Dom : T.Obj) (Fst : (T.Hom Dom Dom).Obj) (η : (T.Hom Dom Dom).Hom (𝟏_(T) Dom) (Fst)) (μ : (T.Hom Dom Dom).Hom (Fst •_(T) Fst) (Fst)) : Prop := sorry -- μ ∘ (η ∙ (𝟙 T)) = 𝟙 T


-- the second identity law for a monad
def MonId₂ (T : twocategory) (Dom : T.Obj) (Fst : (T.Hom Dom Dom).Obj) (η : (T.Hom Dom Dom).Hom (𝟏_(T) Dom) (Fst)) (μ : (T.Hom Dom Dom).Hom (Fst •_(T) Fst) (Fst)) : Prop := sorry -- μ ∘ ((𝟙 T) • η) = 𝟙 T


-- the associativity law for a monad
def MonAss (T : twocategory) (Dom : T.Obj) (Fst : (T.Hom Dom Dom).Obj) (η : (T.Hom Dom Dom).Hom (𝟏_(T) Dom) (Fst)) (μ : (T.Hom Dom Dom).Hom (Fst •_(T) Fst) Fst) : Prop := sorry -- μ ∘ (μ • (𝟙 T)) = μ ∘ ((𝟙 T) • μ)


-- definition of a monad
structure monad (T : twocategory) where
  Dom : T.Obj
  Fst : (T.Hom Dom Dom).Obj
  η : (T.Hom Dom Dom).Hom (𝟏_(T) Dom) Fst
  μ : (T.Hom Dom Dom).Hom (Fst •_(T) Fst) Fst
  Id₁ : MonId₁ T Dom Fst η μ
  Id₂ : MonId₂ T Dom Fst η μ
  Ass : MonAss T Dom Fst η μ


def Mon (C : category) : Type := sorry


-- the first identity law for a monad
def ComId₁ (T : twocategory) (Cod : T.Obj) (Snd : (T.Hom Cod Cod).Obj) (ε : (T.Hom Cod Cod).Hom Snd (𝟏_(T) Cod)) (δ : (T.Hom Cod Cod).Hom Snd (Snd •_(T) Snd)) : Prop := sorry -- μ ∘ (η ∙ (𝟙 T)) = 𝟙 T


-- the second identity law for a monad
def ComId₂ (T : twocategory) (Cod : T.Obj) (Snd : (T.Hom Cod Cod).Obj) (ε : (T.Hom Cod Cod).Hom Snd (𝟏_(T) Cod)) (δ : (T.Hom Cod Cod).Hom Snd (Snd •_(T) Snd)) : Prop := sorry -- μ ∘ ((𝟙 T) • η) = 𝟙 T


-- the associativity law for a monad
def ComAss (T : twocategory) (Cod : T.Obj) (Snd : (T.Hom Cod Cod).Obj) (ε : (T.Hom Cod Cod).Hom Snd (𝟏_(T) Cod)) (δ : (T.Hom Cod Cod).Hom Snd (Snd •_(T) Snd)) : Prop := sorry -- μ ∘ (μ • (𝟙 T)) = μ ∘ ((𝟙 T) • μ)


-- definition of a monad
structure comonad (T : twocategory) where
  Cod : T.Obj
  Snd : (T.Hom Cod Cod).Obj
  ε : (T.Hom Cod Cod).Hom Snd (𝟏_(T) Cod)
  δ : (T.Hom Cod Cod).Hom Snd (Snd •_(T) Snd)
  Id₁ : ComId₁ T Cod Snd ε δ
  Id₂ : ComId₂ T Cod Snd ε δ
  Ass : ComAss T Cod Snd ε δ


-- defining the domain component of the monad corresponding to an adjunction
def MonAdjDom (T : twocategory) (f : adjunction T) : T.Obj := f.Dom


-- defining the functor component of the monad corresponding to an adjunction
def MonAdjFst (T : twocategory) (f : adjunction T) : (T.Hom (MonAdjDom T f) (MonAdjDom T f)).Obj := sorry


-- defining the unit component of the monad corresponding to an adjunction
def MonAdjη (T : twocategory) (f : adjunction T) : (T.Hom (MonAdjDom T f) (MonAdjDom T f)).Hom (𝟏_(T) (MonAdjDom T f)) (MonAdjFst T f) := sorry


-- defining the multiplication component of the monad corresponding to an adjunction
def MonAdjμ (T : twocategory) (f : adjunction T) : (T.Hom (MonAdjDom T f) (MonAdjDom T f)).Hom ((MonAdjFst T f) •_(T) (MonAdjFst T f)) (MonAdjFst T f)  := sorry


-- defining the first identity component of the monad corresponding to an adjunction
def MonAdjId₁ (T : twocategory) (f : adjunction T) : MonId₁ T (MonAdjDom T f) (MonAdjFst T f) (MonAdjη T f) (MonAdjμ T f) := sorry


-- defining the second identity component of the monad corresponding to an adjunction
def MonAdjId₂ (T : twocategory) (f : adjunction T) : MonId₂ T (MonAdjDom T f) (MonAdjFst T f) (MonAdjη T f) (MonAdjμ T f) := sorry


-- defining the associativity component of the monad corresponding to an adjunction
def MonAdjAss (T : twocategory) (f : adjunction T) : MonAss T (MonAdjDom T f) (MonAdjFst T f) (MonAdjη T f) (MonAdjμ T f) := sorry


-- the monad corresponding to an adjunction 
def MonAdj (T : twocategory) (f : adjunction T) : monad T := {Dom := MonAdjDom T f, Fst := MonAdjFst T f, η := MonAdjη T f, μ := MonAdjμ T f, Id₁ := MonAdjId₁ T f, Id₂ := MonAdjId₂ T f, Ass := MonAdjAss T f}


notation : 2000 "?_(" T ")" => MonAdj T

notation : 2000 "?" => MonAdj 𝐂𝐚𝐭


-- defining the domain component of the monad corresponding to an adjunction
def ComAdjCod (T : twocategory) (f : adjunction T) : T.Obj := f.Cod


-- defining the functor component of the monad corresponding to an adjunction
def ComAdjSnd (T : twocategory) (f : adjunction T) : (T.Hom (ComAdjCod T f) (ComAdjCod T f)).Obj := sorry


-- defining the unit component of the monad corresponding to an adjunction
def ComAdjε (T : twocategory) (f : adjunction T) : (T.Hom (ComAdjCod T f) (ComAdjCod T f)).Hom (ComAdjSnd T f) (𝟏_(T) (ComAdjCod T f)) := sorry


-- defining the multiplication component of the monad corresponding to an adjunction
def ComAdjδ (T : twocategory) (f : adjunction T) : (T.Hom (ComAdjCod T f) (ComAdjCod T f)).Hom (ComAdjSnd T f) ((ComAdjSnd T f) •_(T) (ComAdjSnd T f)) := sorry


-- defining the first identity component of the monad corresponding to an adjunction
def ComAdjId₁ (T : twocategory) (f : adjunction T) : ComId₁ T (ComAdjCod T f) (ComAdjSnd T f) (ComAdjε T f) (ComAdjδ T f) := sorry


-- defining the second identity component of the comonad corresponding to an adjunction
def ComAdjId₂ (T : twocategory) (f : adjunction T) : ComId₂ T (ComAdjCod T f) (ComAdjSnd T f) (ComAdjε T f) (ComAdjδ T f) := sorry


-- defining the associativity component of the comonad corresponding to an adjunction
def ComAdjAss (T : twocategory) (f : adjunction T) : ComAss T (ComAdjCod T f) (ComAdjSnd T f) (ComAdjε T f) (ComAdjδ T f) := sorry


-- the comonad corresponding to an adjunction 
def ComAdj (T : twocategory) (f : adjunction T) : comonad T := {Cod := ComAdjCod T f, Snd := ComAdjSnd T f, ε := ComAdjε T f, δ := ComAdjδ T f, Id₁ := ComAdjId₁ T f, Id₂ := ComAdjId₂ T f, Ass := ComAdjAss T f}


-- ¿

notation "¿_(" T ")" => ComAdj T

notation "¿" => ComAdj 𝐂𝐚𝐭


-- defining the object component of the codomain of the Eilenberg-Moore adjunction for Cat
def AdjMonCodObj (f : monad 𝐂𝐚𝐭) : Type := sorry


-- defining the hom component of the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjMonCodHom (f : monad 𝐂𝐚𝐭) (_: AdjMonCodObj f)  (_: AdjMonCodObj f) : Type := sorry


-- defining the identity component of the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjMonCodIdn (f : monad 𝐂𝐚𝐭) (X : AdjMonCodObj f) : AdjMonCodHom f X X := sorry


-- defining the composition component of the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjMonCodCmp (f : monad 𝐂𝐚𝐭) (X : AdjMonCodObj f) (Y : AdjMonCodObj f) (Z : AdjMonCodObj f) (_ : AdjMonCodHom f X Y) (_ : AdjMonCodHom f Y Z) : AdjMonCodHom f X Z := sorry


-- proving the first identity law for the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjMonCodId₁ (f : monad 𝐂𝐚𝐭) (X : AdjMonCodObj f) (Y : AdjMonCodObj f) (f_1 : AdjMonCodHom f X Y) : ((AdjMonCodCmp f) X Y Y f_1 ((AdjMonCodIdn f) Y)) = f_1 := sorry


-- proving the second identity law for the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjMonCodId₂ (f : monad 𝐂𝐚𝐭) (X : AdjMonCodObj f) (Y : AdjMonCodObj f) (f_1 : AdjMonCodHom f X Y) : ((AdjMonCodCmp f) X X Y ((AdjMonCodIdn f) X) f_1 = f_1 ) := sorry


-- proving associativity for the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjMonCodAss (f : monad 𝐂𝐚𝐭) (W : AdjMonCodObj f) (X : AdjMonCodObj f) (Y : AdjMonCodObj f) (Z : AdjMonCodObj f) (f_1 : AdjMonCodHom f W X) (g : AdjMonCodHom f X Y) (h : AdjMonCodHom f Y Z) : (AdjMonCodCmp f W X Z f_1 ((AdjMonCodCmp f) X Y Z g h) = (AdjMonCodCmp f) W Y Z ((AdjMonCodCmp f) W X Y f_1 g) h) := sorry


def AdjMonCod (f : monad 𝐂𝐚𝐭) : 𝐂𝐚𝐭.Obj := {Obj := AdjMonCodObj f, Hom := AdjMonCodHom f, Idn := AdjMonCodIdn f, Cmp := AdjMonCodCmp f, Id₁ := AdjMonCodId₁ f, Id₂ := AdjMonCodId₂ f, Ass := AdjMonCodAss f}


-- constructing the left adjoint of the Eilenberg-Moore adjunction in Cat on objects
def AdjMonFstObj (f : monad 𝐂𝐚𝐭) : f.Dom.Obj → (AdjMonCod f).Obj := sorry


-- constructing the left adjoint of the Eilenberg-Moore adjunction in Cat on morphisms
def AdjMonFstHom (f : monad 𝐂𝐚𝐭) (X : f.Dom.Obj) (Y : f.Dom.Obj) (_ : f.Dom.Hom X Y) : (AdjMonCod f).Hom (AdjMonFstObj f X) (AdjMonFstObj f Y) := sorry


-- proving the first identity law for the left adjoint of the Eilenberg-Moore adjunction in Cat
def AdjMonFstIdn (f : monad 𝐂𝐚𝐭) (X : f.Dom.Obj) : AdjMonFstHom f X X (f.Dom.Idn X) = (AdjMonCod f).Idn (AdjMonFstObj f X) := sorry


-- proving the compositionality law for the left adjoint of Eilenberg-Moore adjunction in Cat
def AdjMonFstCmp (f : monad 𝐂𝐚𝐭) (X : f.Dom.Obj) (Y : f.Dom.Obj) (Z : f.Dom.Obj) (f_1 : f.Dom.Hom X Y) (g : f.Dom.Hom Y Z) :
  (AdjMonCod f).Cmp (AdjMonFstObj f X) (AdjMonFstObj f Y) (AdjMonFstObj f Z)
      (AdjMonFstHom f X Y f_1) (AdjMonFstHom f Y Z g) = AdjMonFstHom f X Z (f.Dom.Cmp X Y Z f_1 g) := sorry


-- assembling the left adjoint of the Eilenberg-Moore adjunction in Cat
def AdjMonFst (f : monad 𝐂𝐚𝐭) : (𝐂𝐚𝐭.Hom f.Dom (AdjMonCod f)).Obj := {Obj := AdjMonFstObj f, Hom := AdjMonFstHom f, Idn := AdjMonFstIdn f, Cmp := AdjMonFstCmp f}


-- constructing the right adjoint of the Eilenberg-Moore adjunction in Cat on objects
def AdjMonSndObj (f : monad 𝐂𝐚𝐭) : (AdjMonCod f).Obj → f.Dom.Obj := sorry


-- constructing the right adjoint of the Eilenberg-Moore adjunction in Cat on morphisms
def AdjMonSndHom (f : monad 𝐂𝐚𝐭) (X : (AdjMonCod f).Obj) (Y : (AdjMonCod f).Obj) : (AdjMonCod f).Hom X Y → f.Dom.Hom (AdjMonSndObj f X) (AdjMonSndObj f Y) := sorry


-- proving the first identity law for the right adjoint of the Eilenberg-Moore adjunction in Cat
def AdjMonSndIdn (f : monad 𝐂𝐚𝐭) (X : (AdjMonCod f).Obj) : (AdjMonSndHom f) X X ((AdjMonCod f).Idn X) = f.Dom.Idn (AdjMonSndObj f X) := sorry


-- proving the compositionality law for the right adjoint of Eilenberg-Moore adjunction in Cat
def AdjMonSndCmp (f : monad 𝐂𝐚𝐭) (X : (AdjMonCod f).Obj) (Y : (AdjMonCod f).Obj) (Z : (AdjMonCod f).Obj) (f_1 : (AdjMonCod f).Hom X Y) (g : (AdjMonCod f).Hom Y Z) : f.Dom.Cmp (AdjMonSndObj f X) (AdjMonSndObj f Y) (AdjMonSndObj f Z) (AdjMonSndHom f X Y f_1) (AdjMonSndHom f Y Z g) = AdjMonSndHom f X Z ((AdjMonCod f).Cmp X Y Z f_1 g) := sorry



-- assembling the right adjoint of the Eilenberg-Moore adjunction in Cat
def AdjMonSnd (f : monad 𝐂𝐚𝐭) : (𝐂𝐚𝐭.Hom (AdjMonCod f) f.Dom).Obj := {Obj := AdjMonSndObj f, Hom := AdjMonSndHom f, Idn := AdjMonSndIdn f, Cmp := AdjMonSndCmp f}


-- constructing the unit of the Eilenberg-Moore adjunction in Cat on objects
def AdjMonηObj (f : monad 𝐂𝐚𝐭) (X : f.Dom.Obj) : f.Dom.Hom ((𝟏_(𝐂𝐚𝐭) f.Dom).Obj X) ((AdjMonSnd f•_(𝐂𝐚𝐭)AdjMonFst f).Obj X) := sorry


-- proving naturality for the unit of the eilenberg moore adjunction unit in Cat
def AdjMonηNat (f : monad 𝐂𝐚𝐭)  (X : f.Dom.Obj) (Y : f.Dom.Obj) (f_1 : f.Dom.Hom X Y) : 
  f.Dom.Cmp (functor.Obj (𝟏_(𝐂𝐚𝐭) f.Dom) X) (functor.Obj (𝟏_(𝐂𝐚𝐭) f.Dom) Y)
      ((AdjMonSnd f•_(𝐂𝐚𝐭)AdjMonFst f).Obj Y) (functor.Hom (𝟏_(𝐂𝐚𝐭) f.Dom) X Y f_1) ((AdjMonηObj f) Y) =
    f.Dom.Cmp ((𝟏_(𝐂𝐚𝐭) f.Dom).Obj X) ((AdjMonSnd f•_(𝐂𝐚𝐭)AdjMonFst f).Obj X)
      ((AdjMonSnd f•_(𝐂𝐚𝐭)AdjMonFst f).Obj Y) ( (AdjMonηObj f) X)
      ((AdjMonSnd f•_(𝐂𝐚𝐭)AdjMonFst f).Hom X Y f_1) := sorry


-- assembling the unit of the eilenberg moore adjunction in Cat
def AdjMonη (f : monad 𝐂𝐚𝐭) : (𝐂𝐚𝐭.Hom f.Dom f.Dom).Hom (𝟏_(𝐂𝐚𝐭) f.Dom) ((AdjMonSnd f)•_(𝐂𝐚𝐭)(AdjMonFst f)) := {Obj := AdjMonηObj f, Nat := AdjMonηNat f}



-- constructing the counit of the eilenberg moore adjunction in Cat on objects
def AdjMonεObj (f : monad 𝐂𝐚𝐭) (X : (AdjMonCod f).Obj) : (AdjMonCod f).Hom ((AdjMonFst f•_(𝐂𝐚𝐭)AdjMonSnd f).Obj X) ((𝟏_(𝐂𝐚𝐭) (AdjMonCod f)).Obj X) := sorry



-- proving naturality for the counit of the eilenberg moore adjunction in Cat
def AdjMonεNat (f : monad 𝐂𝐚𝐭)  (X : (AdjMonCod f).Obj) (Y : (AdjMonCod f).Obj) (f_1 : (AdjMonCod f).Hom X Y) : 
  category.Cmp (AdjMonCod f) (functor.Obj (AdjMonFst f•_(𝐂𝐚𝐭)AdjMonSnd f) X)
      (functor.Obj (AdjMonFst f•_(𝐂𝐚𝐭)AdjMonSnd f) Y) (functor.Obj (𝟏_(𝐂𝐚𝐭) (AdjMonCod f)) Y)
      (functor.Hom (AdjMonFst f•_(𝐂𝐚𝐭)AdjMonSnd f) X Y f_1) ((AdjMonεObj f) Y) =
    category.Cmp (AdjMonCod f) (functor.Obj (AdjMonFst f•_(𝐂𝐚𝐭)AdjMonSnd f) X) (functor.Obj (𝟏_(𝐂𝐚𝐭) (AdjMonCod f)) X)
      (functor.Obj (𝟏_(𝐂𝐚𝐭) (AdjMonCod f)) Y) ((AdjMonεObj f) X) (functor.Hom (𝟏_(𝐂𝐚𝐭) (AdjMonCod f)) X Y f_1) := sorry


-- assembling the counit of the eilenberg moore adjunction in Cat
def AdjMonε (f : monad 𝐂𝐚𝐭) : (𝐂𝐚𝐭.Hom (AdjMonCod f) (AdjMonCod f)).Hom ((AdjMonFst f)•_(𝐂𝐚𝐭)(AdjMonSnd f)) (𝟏_(𝐂𝐚𝐭) (AdjMonCod f))  := {Obj := AdjMonεObj f, Nat := AdjMonεNat f}


-- the coeilenberg comoore adjunction in Cat triangle identity 1
def AdjMonId₁ (f : monad 𝐂𝐚𝐭) : AdjId₁ 𝐂𝐚𝐭 (f.Dom) (AdjMonCod f) (AdjMonFst f) (AdjMonSnd f) (AdjMonη f) (AdjMonε f) := sorry


-- the coeilenberg comoore adjunction in Cat triangle identity 1
def AdjMonId₂ (f : monad 𝐂𝐚𝐭) : AdjId₂ 𝐂𝐚𝐭 (f.Dom) (AdjMonCod f) (AdjMonFst f) (AdjMonSnd f) (AdjMonη f) (AdjMonε f) := sorry


-- assembling the Eilenberg-Moore adjunction in Cat
def exponential (f : monad 𝐂𝐚𝐭) : adjunction 𝐂𝐚𝐭 := {Dom := f.Dom, Cod := AdjMonCod f, Fst := AdjMonFst f, Snd := AdjMonSnd f, η := AdjMonη f, ε := AdjMonε f, Id₁ := AdjMonId₁ f, Id₂ := AdjMonId₂ f}


-- notation for the Eilenberg-Moore categrory in Cat
notation : 2000 "!_(𝐂𝐚𝐭)" M => exponential M


-- defining the object component of the codomain of the Eilenberg-Moore adjunction for Cat
def AdjComDomObj (f : comonad 𝐂𝐚𝐭) : Type := sorry


-- defining the hom component of the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjComDomHom (f : comonad 𝐂𝐚𝐭) (_: AdjComDomObj f)  (_: AdjComDomObj f) : Type := sorry


-- defining the identity component of the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjComDomIdn (f : comonad 𝐂𝐚𝐭) (X : AdjComDomObj f) : AdjComDomHom f X X := sorry


-- defining the composition component of the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjComDomCmp (f : comonad 𝐂𝐚𝐭) (X : AdjComDomObj f) (Y : AdjComDomObj f) (Z : AdjComDomObj f) (_ : AdjComDomHom f X Y) (_ : AdjComDomHom f Y Z) : AdjComDomHom f X Z := sorry


-- proving the first identity law for the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjComDomId₁ (f : comonad 𝐂𝐚𝐭) (X : AdjComDomObj f) (Y : AdjComDomObj f) (f_1 : AdjComDomHom f X Y) : ((AdjComDomCmp f) X Y Y f_1 ((AdjComDomIdn f) Y)) = f_1 := sorry


-- proving the second identity law for the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjComDomId₂ (f : comonad 𝐂𝐚𝐭) (X : AdjComDomObj f) (Y : AdjComDomObj f) (f_1 : AdjComDomHom f X Y) : ((AdjComDomCmp f) X X Y ((AdjComDomIdn f) X) f_1 = f_1 ) := sorry


-- proving associativity for the codomain of the Eilenberg-Moore adjunction for Cat 
def AdjComDomAss (f : comonad 𝐂𝐚𝐭) (W : AdjComDomObj f) (X : AdjComDomObj f) (Y : AdjComDomObj f) (Z : AdjComDomObj f) (f_1 : AdjComDomHom f W X) (g : AdjComDomHom f X Y) (h : AdjComDomHom f Y Z) : (AdjComDomCmp f W X Z f_1 ((AdjComDomCmp f) X Y Z g h) = (AdjComDomCmp f) W Y Z ((AdjComDomCmp f) W X Y f_1 g) h) := sorry


def AdjComDom (f : comonad 𝐂𝐚𝐭) : 𝐂𝐚𝐭.Obj := {Obj := AdjComDomObj f, Hom := AdjComDomHom f, Idn := AdjComDomIdn f, Cmp := AdjComDomCmp f, Id₁ := AdjComDomId₁ f, Id₂ := AdjComDomId₂ f, Ass := AdjComDomAss f}


-- constructing the right adjoint of the Eilenberg-Moore adjunction in Cat on objects
def AdjComFstObj (f : comonad 𝐂𝐚𝐭) : (AdjComDom f).Obj → f.Cod.Obj := sorry


-- constructing the right adjoint of the Eilenberg-Moore adjunction in Cat on morphisms
def AdjComFstHom (f : comonad 𝐂𝐚𝐭) (X : (AdjComDom f).Obj) (Y : (AdjComDom f).Obj) : (AdjComDom f).Hom X Y → f.Cod.Hom (AdjComFstObj f X) (AdjComFstObj f Y) := sorry


-- proving the first identity law for the right adjoint of the Eilenberg-Moore adjunction in Cat
def AdjComFstIdn (f : comonad 𝐂𝐚𝐭) (X : (AdjComDom f).Obj) : (AdjComFstHom f) X X ((AdjComDom f).Idn X) = f.Cod.Idn (AdjComFstObj f X) := sorry


-- proving the compositionality law for the right adjoint of Eilenberg-Moore adjunction in Cat
def AdjComFstCmp (f : comonad 𝐂𝐚𝐭) (X : (AdjComDom f).Obj) (Y : (AdjComDom f).Obj) (Z : (AdjComDom f).Obj) (f_1 : (AdjComDom f).Hom X Y) (g : (AdjComDom f).Hom Y Z) : f.Cod.Cmp (AdjComFstObj f X) (AdjComFstObj f Y) (AdjComFstObj f Z) (AdjComFstHom f X Y f_1) (AdjComFstHom f Y Z g) = AdjComFstHom f X Z ((AdjComDom f).Cmp X Y Z f_1 g) := sorry



-- assembling the right adjoint of the Eilenberg-Moore adjunction in Cat
def AdjComFst (f : comonad 𝐂𝐚𝐭) : (𝐂𝐚𝐭.Hom (AdjComDom f) f.Cod).Obj := {Obj := AdjComFstObj f, Hom := AdjComFstHom f, Idn := AdjComFstIdn f, Cmp := AdjComFstCmp f}


-- constructing the left adjoint of the Eilenberg-Moore adjunction in Cat on objects
def AdjComSndObj (f : comonad 𝐂𝐚𝐭) : f.Cod.Obj → (AdjComDom f).Obj := sorry


-- constructing the left adjoint of the Eilenberg-Moore adjunction in Cat on morphisms
def AdjComSndHom (f : comonad 𝐂𝐚𝐭) (X : f.Cod.Obj) (Y : f.Cod.Obj) (_ : f.Cod.Hom X Y) : (AdjComDom f).Hom (AdjComSndObj f X) (AdjComSndObj f Y) := sorry


-- proving the first identity law for the left adjoint of the Eilenberg-Moore adjunction in Cat
def AdjComSndIdn (f : comonad 𝐂𝐚𝐭) (X : f.Cod.Obj) : AdjComSndHom f X X (f.Cod.Idn X) = (AdjComDom f).Idn (AdjComSndObj f X) := sorry


-- proving the compositionality law for the left adjoint of Eilenberg-Moore adjunction in Cat
def AdjComSndCmp (f : comonad 𝐂𝐚𝐭) (X : f.Cod.Obj) (Y : f.Cod.Obj) (Z : f.Cod.Obj) (f_1 : f.Cod.Hom X Y) (g : f.Cod.Hom Y Z) :
  (AdjComDom f).Cmp (AdjComSndObj f X) (AdjComSndObj f Y) (AdjComSndObj f Z)
      (AdjComSndHom f X Y f_1) (AdjComSndHom f Y Z g) = AdjComSndHom f X Z (f.Cod.Cmp X Y Z f_1 g) := sorry


-- assembling the right adjoint of the Eilenberg-Moore adjunction in Cat
def AdjComSnd (f : comonad 𝐂𝐚𝐭) : (𝐂𝐚𝐭.Hom f.Cod (AdjComDom f)).Obj := {Obj := AdjComSndObj f, Hom := AdjComSndHom f, Idn := AdjComSndIdn f, Cmp := AdjComSndCmp f}


def AdjComηObj (f : comonad 𝐂𝐚𝐭) (X : (AdjComDom f).Obj)  : (AdjComDom f).Hom ((𝟏_(𝐂𝐚𝐭) (AdjComDom f)).Obj X) ((AdjComSnd f•_(𝐂𝐚𝐭)AdjComFst f).Obj X) := sorry


def AdjComηNat (f : comonad 𝐂𝐚𝐭) (X : (AdjComDom f).Obj)  (Y : (AdjComDom f).Obj) (f_1 : category.Hom (AdjComDom f) X Y) : 
  category.Cmp (AdjComDom f) (functor.Obj (𝟏_(𝐂𝐚𝐭) (AdjComDom f)) X) (functor.Obj (𝟏_(𝐂𝐚𝐭) (AdjComDom f)) Y)
      (functor.Obj (AdjComSnd f•_(𝐂𝐚𝐭)AdjComFst f) Y) (functor.Hom (𝟏_(𝐂𝐚𝐭) (AdjComDom f)) X Y f_1)
      (AdjComηObj f Y) =
    category.Cmp (AdjComDom f) (functor.Obj (𝟏_(𝐂𝐚𝐭) (AdjComDom f)) X) (functor.Obj (AdjComSnd f•_(𝐂𝐚𝐭)AdjComFst f) X)
      (functor.Obj (AdjComSnd f•_(𝐂𝐚𝐭)AdjComFst f) Y) (AdjComηObj f X)
      (functor.Hom (AdjComSnd f•_(𝐂𝐚𝐭)AdjComFst f) X Y f_1) := sorry


-- assembling the unit of the eilenberg moore adjunction in Cat
def AdjComη (f : comonad 𝐂𝐚𝐭) : (𝐂𝐚𝐭.Hom (AdjComDom f) (AdjComDom f)).Hom (𝟏_(𝐂𝐚𝐭) (AdjComDom f)) ((AdjComSnd f)•_(𝐂𝐚𝐭)(AdjComFst f)) := {Obj := AdjComηObj f, Nat := AdjComηNat f}


def AdjComεObj (f : comonad 𝐂𝐚𝐭) (X : f.Cod.Obj) : f.Cod.Hom ((AdjComFst f•_(𝐂𝐚𝐭)AdjComSnd f).Obj X) ((𝟏_(𝐂𝐚𝐭) f.Cod).Obj X) := sorry


def AdjComεNat (f : comonad 𝐂𝐚𝐭) (X : f.Cod.Obj) (Y : f.Cod.Obj) (f_1 : category.Hom f.Cod X Y) : 
  category.Cmp f.Cod (functor.Obj (AdjComFst f•_(𝐂𝐚𝐭)AdjComSnd f) X) (functor.Obj (AdjComFst f•_(𝐂𝐚𝐭)AdjComSnd f) Y)
      (functor.Obj (𝟏_(𝐂𝐚𝐭) f.Cod) Y) (functor.Hom (AdjComFst f•_(𝐂𝐚𝐭)AdjComSnd f) X Y f_1) (AdjComεObj f Y) =
    category.Cmp f.Cod (functor.Obj (AdjComFst f•_(𝐂𝐚𝐭)AdjComSnd f) X) (functor.Obj (𝟏_(𝐂𝐚𝐭) f.Cod) X)
      (functor.Obj (𝟏_(𝐂𝐚𝐭) f.Cod) Y) (AdjComεObj f X) (functor.Hom (𝟏_(𝐂𝐚𝐭) f.Cod) X Y f_1) := sorry


-- assembling the counit of the eilenberg moore adjunction in Cat
def AdjComε (f : comonad 𝐂𝐚𝐭) : (𝐂𝐚𝐭.Hom f.Cod f.Cod).Hom ((AdjComFst f)•_(𝐂𝐚𝐭)(AdjComSnd f)) (𝟏_(𝐂𝐚𝐭) f.Cod)  := {Obj := AdjComεObj f, Nat := AdjComεNat f}


-- the coeilenberg comoore adjunction in Cat triangle identity 1
def AdjComId₁ (f : comonad 𝐂𝐚𝐭) : AdjId₁ 𝐂𝐚𝐭 (AdjComDom f) f.Cod (AdjComFst f) (AdjComSnd f) (AdjComη f) (AdjComε f) := sorry


-- the coeilenberg comoore adjunction in Cat triangle identity 2
def AdjComId₂ (f : comonad 𝐂𝐚𝐭) : AdjId₂ 𝐂𝐚𝐭 (AdjComDom f) f.Cod (AdjComFst f) (AdjComSnd f) (AdjComη f) (AdjComε f) := sorry



def coexponential (f : comonad 𝐂𝐚𝐭) : adjunction 𝐂𝐚𝐭 := {Dom := (AdjComDom f), Cod := f.Cod, Fst := AdjComFst f, Snd := AdjComSnd f, η := AdjComη f, ε := AdjComε f, Id₁ := AdjComId₁ f, Id₂ := AdjComId₂ f}


-- notation for the co-Eilenberg-Moore categrory in Cat
notation : 2000 "¡_(𝐂𝐚𝐭)" => coexponential


variable {f : adjunction 𝐂𝐚𝐭}

/-
variable {Φ : adjunction 𝐂𝐚𝐭}
-/


-- constructing the canonical map out of the codomain of the eilenberg moore adjunction in Cat
def Exp (f : adjunction 𝐂𝐚𝐭) : (!_(𝐂𝐚𝐭) ?_(𝐂𝐚𝐭) A).Cod ⭢ A.Cod := sorry


-- notation for the canonical map from eilenberg moore category of the corresponding monad for an adjunction
notation "ꜝ" f => Exp f


-- proving the universal property of the eilenberg-moore adjunction in Cat
-- theorem universal_property_of_the_eilenberg_moore_adjunction (φ:adjunction) : ∃!(F : functor (!?φ).Cod φ.Cod),F •_(Cat) (!?φ)𛲔 = (φ𛲔) := sorry


-- def Cxp (f : adjunction 𝐂𝐚𝐭) : (¡_(𝐂𝐚𝐭) (¿_(𝐂𝐚𝐭) P)). ⭢ P := sorry


-- notation for the canonical map from co-Eilenberg-co-Moore category of the corresponding monad for an adjunction
-- notation "ꜞ" => Cxp


-- proving the universal property of the co-Eilenberg-co-Moore adjunction in Cat
/-
def 
-/


-- defining monadicity
-- def monadic_adjunction (C : twocategory) (f : adjunction C) : Prop := sorry


-- !M is monadic
/-

-/


-- defining comonadic adjunction
-- def comonadic (C : twocategory) (f : adjunction C) : Prop := sorry


-- comonadicity of a monad
/-

-/


-- ¡M is comonadic
/-

-/


-- defining a bimonadic adjunction
--structure bimonadic_adjunction where
--  f : adjunction
--  Mon : functor (?f)ꜝ  -- need to replace the first Cod with (?f)ꜝ
--  Com : 




-- defining the cartesian closed category structure
structure cartesian_closed_category where
  Obj : 𝐂𝐚𝐭.Obj
  Prd : Obj.Obj → (𝐂𝐚𝐭.Hom Obj Obj).Obj
  Hom : Obj.Obj → (𝐂𝐚𝐭.Hom Obj Obj).Obj
  η : (X : Obj.Obj) → (𝐂𝐚𝐭.Hom Obj Obj).Hom (𝟏_(𝐂𝐚𝐭) Obj) (Hom X •_(𝐂𝐚𝐭) Prd X)
--  ε : (X : Obj.Obj) → (𝐂𝐚𝐭.Hom Obj Obj).Hom (Prd X •_(𝐂𝐚𝐭) Hom X) (𝟏_(𝐂𝐚𝐭) Obj))
--  Id₁ : 
--  Id₂ : 
  Pnt : Obj.Obj
--  Id₁ : (Prd Pnt) ≅_(𝐂𝐚𝐭.Hom Obj Obj) (𝟙_Cat Obj)
--  Id₂ : (Hom Pnt) ≅_(𝐂𝐚𝐭.Hom Obj Obj) (𝟙_Cat Obj)
  ComΔ : (X : Obj.Obj) → (𝐂𝐚𝐭.Hom Obj Obj).Hom (Prd X) (Prd X •_(𝐂𝐚𝐭) Prd X)
  Comε : (X : Obj.Obj) → (𝐂𝐚𝐭.Hom Obj Obj).Hom (Prd X) (𝟏_(𝐂𝐚𝐭) Obj)
--  ComId₁ : 
--  ComId₂ : 
--  ComAss : 
  Monη : (X : Obj.Obj) → (𝐂𝐚𝐭.Hom Obj Obj).Hom (Hom X) (𝟏_(𝐂𝐚𝐭) Obj)
  Monμ : (X : Obj.Obj) → (𝐂𝐚𝐭.Hom Obj Obj).Hom (Hom X •_(𝐂𝐚𝐭) Hom X) (Hom X)
--  MonId₁ : 
--  MonId₂ : 
--  MonAss : 
--  Tw₁ : (X : Obj.Obj) → (Y : Obj.Obj) → ((Prd X) •_Cat (Prd Y)) ≅_(𝐂𝐚𝐭.Hom Obj Obj) ((Prd Y) •_Cat (Prd X))
--  Tw₂ : (X : Obj.Obj) → (Y : Obj.Obj) → ((Hom X) •_Cat (Hom Y)) ≅_(𝐂𝐚𝐭.Hom Obj Obj) ((Hom Y) •_Cat (Hom X))





/-

My cartesian closed category is provisional. Here I keep a list of those 𝐂𝐚𝐭.Obj, category =  which form cartesian closed categories

EXAMPLE   | Description
----------------------------------------------
Set       | the category of sets
Cat       | the category of categories
∞-Cat     | the category of ∞-categories
D(∞-Cat/*)| the derived category of ∞-categories

I would like to base my library around the characterization of cartesian product, in which pairs (C.Hom X Y₁) × (C.Hom X Y₂) correspond naturally to maps P → A × B for an associative unitial adjoint operation ×. However, I want to include Fox's theorem.

-/



-- definition of product of objects
-- def product (C : 𝐂𝐚𝐭.Obj) (Y₁ : C.Obj) (Y₂ : C.Obj) : ∀(X : C.Obj),∀(f₁ : C.Hom X Y₁),∀(f₂ : C.Hom X Y₂),∃(f : C.Hom X ((C.Prd Y₁).Obj Y₂)),


-- definition of product of morphisms
-- def product (C : 𝐂𝐚𝐭.Obj) (X : C.Obj) (Y : C.Obj) 


-- Defining the canonical map in the universal property of Prd
-- def 


-- Proving the uniqueness of the canonical map in the universal property of Prd
/-
theorem (uniqueness of the canonical map)
- first of all, how do you define the canonical map as a natural transformation?
- 
-/



structure pullback_system where
  Obj : 𝐂𝐚𝐭.Obj
  Pnt : Obj.Obj
  CmpObj : Obj.Obj → 
        𝐂𝐚𝐭.Obj
  CmpHom : (C : Obj.Obj) → 
        (D : Obj.Obj) → 
        (F : Obj.Hom C D) → 
        (𝐂𝐚𝐭.Hom (CmpObj C) (CmpObj D)).Obj
  CmpIdn : (C : Obj.Obj) → ((CmpHom C C (𝟙_(Obj) C)) = 𝟏_(𝐂𝐚𝐭) (CmpObj C))
  CmpCmp : (C : Obj.Obj) → (D : Obj.Obj) → (E : Obj.Obj) → (F : Obj.Hom C D) → (G : Obj.Hom D E) → (((CmpHom D E G) •_(𝐂𝐚𝐭) (CmpHom C D F)) = CmpHom C E (G ∘_(Obj) F))
  Fix : Obj = (CmpObj Pnt)
  Pul : (C : Obj.Obj) → 
        (D : Obj.Obj) → 
        (F : Obj.Hom C D) → 
        (𝐂𝐚𝐭.Hom (CmpObj D) (CmpObj C)).Obj
  η : (C : Obj.Obj) → (D : Obj.Obj) → (F : Obj.Hom C D) → ((𝐂𝐚𝐭.Hom (CmpObj C) (CmpObj C)).Hom (𝟏_(𝐂𝐚𝐭) (CmpObj C)) ((Pul C D F) •_(𝐂𝐚𝐭) (CmpHom C D F)))
  ε : (C : Obj.Obj) → (D : Obj.Obj) → (F : Obj.Hom C D) → ((𝐂𝐚𝐭.Hom (CmpObj D) (CmpObj D)).Hom ((CmpHom C D F) •_(𝐂𝐚𝐭) (Pul C D F)) (𝟏_(𝐂𝐚𝐭) (CmpObj D)))
  Id₁ : (C : Obj.Obj) → (D : Obj.Obj) → (F : Obj.Hom C D) → (AdjId₁ 𝐂𝐚𝐭 (CmpObj C) (CmpObj D) (CmpHom C D F) (Pul C D F) (η C D F) (ε C D F))
  Id₂ : (C : Obj.Obj) → (D : Obj.Obj) → (F : Obj.Hom C D) → (AdjId₂ 𝐂𝐚𝐭 (CmpObj C) (CmpObj D) (CmpHom C D F) (Pul C D F) (η C D F) (ε C D F))


-- defining a map of pullback systems
structure PulHom (Γ₁ : pullback_system) (Γ₂ : pullback_system) where
  Obj : Γ₁.Obj ⭢ Γ₂.Obj


-- defining the identity map of two pullback systems
def PulIdn (X : pullback_system) : PulHom X X := sorry


-- defining the composition of two pullback systems
def PulCmp (X : pullback_system) (Y : pullback_system) (Z : pullback_system) (_ : PulHom X Y) (_ : PulHom Y Z) : PulHom X Z := sorry


-- proving the first identity law for maps of pullback systems
def PulId₁ (X : pullback_system) (Y : pullback_system) (f : PulHom X Y) : PulCmp X Y Y f (PulIdn Y) = f := sorry


-- proving the first identity law for maps of pullback systems
def PulId₂ (X : pullback_system) (Y : pullback_system) (f : PulHom X Y) : PulCmp X X Y (PulIdn X) f = f := sorry


def PulAss (W : pullback_system) (X : pullback_system) (Y : pullback_system) (Z : pullback_system) (f : PulHom W X) (g : PulHom X Y) (h : PulHom Y Z) : PulCmp W X Z f (PulCmp X Y Z g h) = PulCmp W Y Z (PulCmp W X Y f g) h := sorry


-- constructing the category Pul of pullback systems
def Pul : category := {Obj := pullback_system, Hom := PulHom, Idn := PulIdn, Cmp := PulCmp, Id₁ := PulId₁, Id₂ := PulId₂, Ass := PulAss}


def D (Γ : pullback_system) := Γ.Obj


notation "D(" Γ ")" => D Γ


def derived_category (Γ : pullback_system) (C : Γ.Obj.Obj) : 𝐂𝐚𝐭.Obj := Γ.CmpObj C


-- notation "Cmp_(" Γ ")" => derived_category Γ
notation "D(" Γ "⁄" C ")" => derived_category Γ C


def pullback (Γ : pullback_system) (E : D(Γ).Obj) (B :  D(Γ).Obj) (f :  D(Γ).Hom E B) : (adjunction 𝐂𝐚𝐭) := sorry


notation : 4000 "p_(" Γ ")" => pullback Γ


-- 
/-
def pIdn : 
-/


--
/-
def pCmp : 
-/


def terminal_object (Γ : pullback_system) : Γ.Obj.Obj := Γ.Pnt


notation : 3000 "*_(" Γ ")" => terminal_object Γ


-- def pullback (Γ : pullback_system) (C₁ : Γ.Obj) (C₂ : Γ.Obj) (D : Γ.Obj) (f₁ : Γ.Hom C₁ D) (f₂ : Γ.Hom C₂ D) : Γ.Obj := sorry


-- notation 


-- definition of pullback on objects
/-
def pullback {C : category} (X : C.Obj) (Y : C.Obj)
-/


-- definition of pullback on morphisms
/-
def pullback {C : category} ...
-/


-- Defining the canonical map in the universal property of Prd
-- def 


-- Proving the uniqueness of the canonical map in the universal property of Prd
/-
theorem (uniqueness of the canonical map)
- first of all, how do you define the canonical map as a natural transformation?
- 
-/



structure overobject_classifier (Γ : pullback_system) where
  Inf : Γ.Obj.Obj
--  Ovr : Γ.Obj.Hom *_(Γ) ∞_(Γ)
--  χ : (C : Obj.Obj) → (Cmp C).Obj → (Obj.Hom C Inf)
--  Cls : (C : Obj.Obj) → (f : (Cmp C).Obj) → ((Pul C Inf (χ C f)).Hom Pnt Inf Ovr = f)


def universe_object (Γ : pullback_system) {O : overobject_classifier Γ} : Γ.Obj.Obj := O.Inf


notation "∞_(" Γ ")" => universe_object Γ


-- defining ⊥_(Γ) : Γ.Obj.Hom *_(Γ) ∞_(Γ)
-- def overobject_classifier (Γ : pullback_system) {O: overobject_classifier Γ} : (Γ.Obj.Hom *_(Γ) ∞_(Γ)) := O.Ovr


-- notation "⊥_(" Γ ")" => overobject_classifier Γ


-- defining χ_(Γ) : ???
-- def characteristic_function (Γ : pullback_system) {_ : overobject_classifier Γ}


-- notation "χ_(" Γ ")" => 


-- 
-- def TwoSetObj : Type := Set


-- defining 𝐒𝐞𝐭.Hom
/-

-/


-- defining 𝐒𝐞𝐭.Idn
/-

-/


-- efining 𝐒𝐞𝐭.Cmp
/-

-/


-- defining 𝐒𝐞𝐭.Id₁
/-

-/


-- defining 𝐒𝐞𝐭.Id₂
/-

-/


-- defining 𝐒𝐞𝐭.Ass
/-

-/












-- definition of an internal category in a pullback system
structure internal_category (Γ : pullback_system) where
  Obj : D(Γ).Obj
  Mor : D(Γ).Obj
-- Dom
-- Cod



-- definition of an internal functor in a pullback system
structure internal_functor (Γ : pullback_system) (C : internal_category Γ) (D : internal_category Γ) where
  Obj : D(Γ).Hom C.Obj D.Obj
-- Mor


-- definition of the identity internal functor in a pullback system
-- def identity_internal_functor (Γ : pullback_system) (C : )


-- definition of the composition of internal functors in a pullback system
/-

-/


-- proving the the first identity law for internal categories in a pullback system
/-

-/


-- proving the second identity law for internal categories in a pullback system
/-

-/


-- proving the associativity law for internal categories in a pullback system
/-

-/


def IntCat (Γ : pullback_system) : 𝐂𝐚𝐭.Obj := sorry


notation : 2000 "Cat_(" Γ ")" => IntCat Γ


-- internal C-sheaves
def internal_sheaf (Γ : pullback_system) (C : Cat_(Γ).Obj) : Type := sorry


-- defining an internal functor between internal C-sheaves
def ShfHom (Γ : pullback_system) (C : Cat_(Γ).Obj) (F : internal_sheaf Γ C) (G : internal_sheaf Γ C) : Type := sorry


-- defining the identity internal functor of an internal C-sheaf
def ShfIdn (Γ : pullback_system) (C : Cat_(Γ).Obj) (F : internal_sheaf Γ C) : ShfHom Γ C F F := sorry


-- defining the composition of internal functors
def ShfCmp (Γ : pullback_system) (C : Cat_(Γ).Obj) (F : internal_sheaf Γ C) (G : internal_sheaf Γ C) (H : internal_sheaf Γ C) (f : ShfHom Γ C F G)  (g : ShfHom Γ C G H) : ShfHom Γ C F H := sorry


-- proving the first identity law for internal functors
def ShfId₁ (Γ : pullback_system) (C : Cat_(Γ).Obj) (X : internal_sheaf Γ C) (Y : internal_sheaf Γ C) (f : ShfHom Γ C X Y) : ((ShfCmp Γ C X Y Y f (ShfIdn Γ C Y)) = f) := sorry


-- proving the second identity law for internal functors
def ShfId₂ (Γ : pullback_system) (C : Cat_(Γ).Obj) (X : internal_sheaf Γ C) (Y : internal_sheaf Γ C) (f : ShfHom Γ C X Y) : ((ShfCmp Γ C X X Y (ShfIdn Γ C X) f) = f) := sorry


-- proving the associativity law for internal functors
def ShfAss (Γ : pullback_system) (C : Cat_(Γ).Obj) (W : internal_sheaf Γ C) (X : internal_sheaf Γ C) (Y : internal_sheaf Γ C) (Z : internal_sheaf Γ C) (f : ShfHom Γ C W X) (g : ShfHom Γ C X Y) (h : ShfHom Γ C Y Z) : (ShfCmp Γ C) W X Z f ((ShfCmp Γ C) X Y Z g h) = (ShfCmp Γ C) W Y Z ((ShfCmp Γ C) W X Y f g) h := sorry


def IntShf (Γ : pullback_system) (C : Cat_(Γ).Obj) : 𝐂𝐚𝐭.Obj := {Obj := internal_sheaf Γ C, Hom := ShfHom Γ C, Idn := ShfIdn Γ C, Cmp := ShfCmp Γ C, Id₁ := ShfId₁ Γ C, Id₂ := ShfId₂ Γ C, Ass := ShfAss Γ C}


notation : 2000 "Shf_(" Γ ")" => IntShf Γ













def path_space (Γ : pullback_system) (E : D(Γ).Obj) (B : D(Γ).Obj) (f : D(Γ).Hom E B) : Cat_(Γ).Obj := sorry


notation "P_(" Γ ")" => path_space Γ


-- defining the Fst component of the internal sheaf principal
-- def descent_equivalenceFst (Γ : pullback_system) (f : Mor_(Γ).Obj) : (𝐂𝐚𝐭.Hom (!_(𝐂𝐚𝐭) (?_(𝐂𝐚𝐭) (¡_(𝐂𝐚𝐭) (¿_(𝐂𝐚𝐭) (p_(Γ) f.Dom f.Cod f.Mor))))).Cod (Shf_(Γ) (ℙ_(Γ).Obj f))).Obj := sorry


-- defining the Snd component of the internal sheaf principal
-- def descent_equivalenceSnd (Γ : pullback_system) (f : Mor_(Γ).Obj) : (𝐂𝐚𝐭.Hom (Shf_(Γ) (ℙ_(Γ).Obj f)) (!_(𝐂𝐚𝐭) (?_(𝐂𝐚𝐭) (¡_(𝐂𝐚𝐭) (¿_(𝐂𝐚𝐭) (p_(Γ) f.Dom f.Cod f.Mor))))).Cod).Obj := sorry






--
-- def descent_equivalenceId₁ (Γ : pullback_system) (f : Mor_(Γ).Obj) : (internal_sheaf_principalSnd Γ f) •_(𝐂𝐚𝐭) (internal_sheaf_principalFst Γ f) = I := sorry






--
/-
def descent_equivalenceId₂ :  := sorry
-/


-- assembling the descent equivalence
def descent_equivalence (Γ : pullback_system) (E : Γ.Obj.Obj) (B : Γ.Obj.Obj) (f : Γ.Obj.Hom E B) : (!_(𝐂𝐚𝐭) (?_(𝐂𝐚𝐭) (¡_(𝐂𝐚𝐭) (¿_(𝐂𝐚𝐭) (p_(Γ) E B f))))).Cod ≃_(𝐂𝐚𝐭) Shf_(Γ) (P_(Γ) E B f) := sorry


notation "♆" => descent_equivalence


-- defining ∞-category
inductive infinity_category where
| Pnt : infinity_category


notation "∞-category" => infinity_category


-- defining ∞-functor (C : ∞-category) (D : ∞-category)
inductive infinity_functor where
| Idn : (C : ∞-category) → infinity_functor


notation "∞-functor" => infinity_functor


-- defining ∞-natural_transformation
inductive infinity_natural_transformation where
| Idn : ∞-functor → infinity_natural_transformation


-- notation for infinity_natural_transformation
notation "∞-natural_transformation" => infinity_natural_transformation


-- defining a homotopy
inductive homotopy where
| Idn : ∞-natural_transformation → homotopy


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


--
/-

-/


def TwoInfCat : twocategory := sorry


notation "∞-𝐂𝐚𝐭" => TwoInfCat


def InfCat : pullback_system := sorry


notation "∞-ℂ𝕒𝕥" => InfCat


def Obj (Γ : pullback_system) := Γ.Obj

notation "∞-Cat" => Obj ∞-ℂ𝕒𝕥


-- def B : Cat_(Γ) ⭢ D(Γ) := sorry


-- def Par (C : D(∞-ℂ𝕒𝕥).Obj) : Shf_(∞-ℂ𝕒𝕥) (P_(∞-ℂ𝕒𝕥) C C (𝟙_(D(∞-ℂ𝕒𝕥)) C)) ⭢ (Cmp_(∞-ℂ𝕒𝕥) C) := sorry


notation "∂" => Par


def internal_category_fixed_point_principal (Γ : pullback_system) : Type := D(Γ) ≃_(ℂ𝕒𝕥) Cat_(Γ)











-- def internal_category_fixed_point_principal_proofId₂ : 


def internal_category_fixed_point_principal_proof : internal_category_fixed_point_principal ∞-ℂ𝕒𝕥 := sorry


def internal_sheaf_fixed_point_principal (Γ : pullback_system) (C : D(Γ).Obj) : Type := Shf_(Γ) (P_(Γ) C C (𝟙_(D(Γ)) C)) ≃_(𝐂𝐚𝐭) (!_(𝐂𝐚𝐭) (?_(𝐂𝐚𝐭) (¡_(𝐂𝐚𝐭) (¿_(𝐂𝐚𝐭) (p_(Γ) C C (𝟙_(D(Γ)) C))))))












-- The internal C-sheaf fixed point principal

/-
Next we prove the internal C-sheaf fixed point principal. This says says that 

            Shf_(∞-ℂ𝕒𝕥) (P_(∞-ℂ𝕒𝕥) C C (𝟙_(D(∞-ℂ𝕒𝕥)) C)) ≃_(𝐂𝐚𝐭) !?¡¿ (p_(∞-ℂ𝕒𝕥) C C (𝟙_(D(∞-ℂ𝕒𝕥)) C))

This theorem is much like the Yoneda lemma (よ-lemma).
-/


def internal_sheaf_fixed_point_principal_proof (C : D(∞-ℂ𝕒𝕥).Obj) : internal_sheaf_fixed_point_principal ∞-ℂ𝕒𝕥 C  := sorry



-- def categorical_whitehead_theorem := sorry










