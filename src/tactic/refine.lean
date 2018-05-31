
import data.dlist

section util

universes u v

def dlist.join {α} : list (dlist α) → dlist α
 | [] := dlist.empty
 | (x :: xs) := x ++ dlist.join xs

variables {m : Type u → Type v} [applicative m]

def mmap₂
  {α₁ α₂ φ : Type u}
  (f : α₁ → α₂ → m φ)
: Π (ma₁ : list α₁) (ma₂: list α₂), m (list φ)
 | (x :: xs) (y :: ys) := (::) <$> f x y <*> mmap₂ xs ys
 | _ _ := pure []

end util

namespace tactic

open interactive interactive.types lean.parser
     tactic.interactive (itactic)
     tactic nat applicative

meta def var_names : expr → list name
 | (expr.pi n _ _ b) := n :: var_names b
 | _ := []

meta def drop_binders : expr → tactic expr
 | (expr.pi n bi t b) := b.instantiate_var <$> mk_local' n bi t >>= drop_binders
 | e := pure e

meta def subobject_names (struct_n : name) : tactic (list name × list name) :=
do env ← get_env,
   [c] ← pure $ env.constructors_of struct_n | fail "too many constructors",
   vs  ← var_names <$> (mk_const c >>= infer_type),
   fields ← env.structure_fields struct_n,
   return $ fields.partition (λ fn, ↑("_" ++ fn.to_string) ∈ vs)

meta def expanded_field_list' : name → tactic (dlist $ name × name) | struct_n :=
do (so,fs) ← subobject_names struct_n,
   ts ← so.mmap (λ n, do
     e ← mk_const (n.update_prefix struct_n) >>= infer_type >>= drop_binders,
     expanded_field_list' $ e.get_app_fn.const_name),
   return $ dlist.join ts ++ dlist.of_list (fs.map $ prod.mk struct_n)
open functor function

meta def expanded_field_list (struct_n : name) : tactic (list $ name × name) :=
dlist.to_list <$> expanded_field_list' struct_n

meta def mk_mvar_list : ℕ → tactic (list expr)
 | 0 := pure []
 | (succ n) := (::) <$> mk_mvar <*> mk_mvar_list n

namespace interactive
open functor
meta def refine_struct (e : parse texpr) (ph : parse $ optional $ tk "with" *> ident) : tactic unit :=
do    str ← e.get_structure_instance_info,
      tgt ← target,
      let struct_n : name := tgt.get_app_fn.const_name,
      exp_fields ← expanded_field_list struct_n,
      let missing_f := exp_fields.filter (λ f, (f.2 : name) ∉ str.field_names),
      let provided  := exp_fields.filter (λ f, (f.2 : name) ∈ str.field_names),
      vs ← mk_mvar_list missing_f.length,
      e' ← to_expr $ pexpr.mk_structure_instance
          { struct := some struct_n
          , field_names  := str.field_names ++ missing_f.map prod.snd
          , field_values := str.field_values ++ vs.map to_pexpr },
      tactic.exact e',
      gs ← with_enable_tags (
        mmap₂ (λ (n : name × name) v, do
           set_goals [v],
           try (interactive.unfold (provided.map $ λ ⟨s,f⟩, f.update_prefix s) (loc.ns [none])),
           apply_auto_param
             <|> apply_opt_param
             <|> (set_main_tag [`_field,n.2,n.1]),
           get_goals)
        missing_f vs),
      set_goals gs.join,
      return ()

meta def get_current_field : tactic name :=
do [_,field,str] ← get_main_tag,
   expr.const_name <$> resolve_name (field.update_prefix str)

meta def let_field : tactic unit :=
get_current_field
>>= mk_const
>>= pose `field none
>>  return ()

meta def have_field : tactic unit :=
get_current_field
>>= mk_const
>>= note `field none
>>  return ()

meta def apply_field : tactic unit :=
get_current_field >>= applyc

end interactive

end tactic
