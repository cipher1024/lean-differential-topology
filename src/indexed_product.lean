import algebra.module
import tactic.refine

universes u v

namespace tactic

open tactic.interactive

meta def derive_field : tactic unit :=
do b ← target >>= is_prop,
   if b then do
     field ← get_current_field,
     intros >> funext,
     applyc field
   else do
     field ← get_current_field,
     xs ← intros <* intro1,
     applyc field,
     xs.mmap' apply

run_cmd add_interactive [`derive_field]

end tactic

-- following does not work, always need (x[i])
-- local notation x`[`:max i`]`:0 := x i
-- it would be nice to have a notation making it clear we don't think of x as a function

namespace indexed_product
variable {I : Type u} -- The indexing type
variable {f : I → Type v}

instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
by refine_struct { .. } ; derive_field

instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
by refine_struct { .. } ; derive_field

instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance add_semigroup [∀ i, add_semigroup $ f i] : add_semigroup (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance add_group [∀ i, add_group $ f i] : add_group (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance add_comm_group [∀ i, add_comm_group $ f i] : add_comm_group (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance distrib [∀ i, distrib $ f i] : distrib (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance ring [∀ i, ring $ f i] : ring (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance comm_ring [∀ i, comm_ring $ f i] : comm_ring (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance has_scalar {α : Type*} [∀ i, has_scalar α $ f i] : has_scalar α (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance module {α : Type*} [ring α] [∀ i, module α $ f i] : module α (Π i : I, f i) :=
by refine_struct { .. } ; try { derive_field }

instance vector_space (α : Type*) [field α] [∀ i, vector_space α $ f i] : vector_space α (Π i : I, f i) :=
{ ..indexed_product.module }

end indexed_product
