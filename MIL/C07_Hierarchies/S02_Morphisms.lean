import MIL.Common
import Mathlib.Topology.Instances.Real

set_option autoImplicit true

-- first attempt at a mechanism to show that some functions are homomorphisms
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'

-- using a structure to name the two constraints
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'

-- With continuity, even though continuous maps are the structure-preserving
-- maps between topological spaces
-- it is frequent in analysis that we deal with maps that are only continuous
-- piecewise (and also discuss continuously differentiable, etc.),
-- so we want to be able to talk about continuity separately from
-- functions between topological spaces
-- hence `Continuous` as a predicate on functions
example : Continuous (id : ℝ → ℝ) := continuous_id

-- in contrast, we bundle homomorphisms with their proof of being structure-preserving
-- the annotation generates extensionality lemmas for the homomorphism
-- so that it can be used with the `ext` tactic
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

-- `CoeFun` is a class of coercion functions; registering a coercion function
-- as an instance under this class allows us to use the function as a coercion
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

-- the `coe` attribute tells Lean to use a nearly indistinct notation ↑ for the coercion
attribute [coe] MonoidHom₁.toFun

-- testing out coercing and back again
example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one

@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

-- we run into issues when we want to define coercions for rings
-- The coercion to the carrier structure should be something like
-- MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁
-- so we do not define a conflicting coercion function
-- more importantly, lemmas about monoid morphisms do not lift to ring morphisms
  -- naively, one option is to require us to go down to monoids and back up to rings whenever we use a ring
  -- and the other is to restate all the lemmas about monoid homomorphisms for ring homomorphisms
@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S


-- mathlib4 uses the following approach: define a class of homomorphisms against
-- which we define our lemmas on monoid homomorphisms between structures that are at least monoids. Then instantiate this class
-- with both monoid homomorphisms and ring homomorphisms.
class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

-- this instantiation is bad, since when faced with a function that needs coercing,
-- Lean will try to search all monoid instances to find one that matches (ranging over all possibilities for M and N)
-- we want to limit the search space to only those where there are instances
-- MonoidHomClass₁ F _ _, where F is of the type of the function we are coercing
def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun

-- hence consider something like this, note the `outParam`, so that Lean tries to infer F before searching for M and N.
class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

-- registering this as a coercion
instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun

-- registering monoid homomorphisms as instances of this class
instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

-- registering ring homomorphisms as instances of this class
instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul

-- proving stuff about monoid homomorphisms
lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

-- showing that it applies to monoid homomorphisms via the coercion
example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

-- showing that it applies to ring homomorphisms via the coercion
example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h


-- we use FunLike to bundle up the coercion machinery, including noting that the coercion map that maps homomorphisms to their carrier set's functions is injective
class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul


@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β] extends
    DFunLike F α (fun _ ↦ β) where
  le_of_le : ∀ (f : F) a a', a ≤ a' → f a ≤ f a'

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where
  coe := OrderPresHom.toFun
  coe_injective' := OrderPresHom.ext
  le_of_le := OrderPresHom.le_of_le

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' := OrderPresMonoidHom.ext
  le_of_le := OrderPresMonoidHom.le_of_le

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β where
  coe := MonoidHom₁.toFun ∘ OrderPresMonoidHom.toMonoidHom₁
  coe_injective' := OrderPresMonoidHom.ext
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
