/-A concise version of m14.lean and m15.lean
Containing theories of Sum exchange and Sum curry, Sum reduced
-/
import data.set data.finset algebra.group_bigops
import aux

local attribute prod.has_decidable_eq[instance]

open prod.ops function

variables {A B C:Type}{a:A}{b:B}
variables [deceqA: decidable_eq A][deceqB: decidable_eq B][c: semiring C]
variables {f:A->B->C}{f': A×B -> C}

namespace finset
  
  variables {s s₁:finset A}{t t₁:finset B}
  include deceqA deceqB c

  /-Sum can exchange-/
  
  --originally l10 in m14.lean
  lemma exSum_aux1 :(∑ x∈∅,∑ y∈t, f x y) = ∑ y∈t, ∑ x∈∅, f x y := 
    by rewrite [Sum_empty,Sum_zero]

  -- originally l11 in m14.lean
  lemma exSum_aux2 (H: a ∉ s):(∑ x∈(insert a s),∑ y∈t, f x y) = 
  (∑ y∈t, f a y) + (∑ x∈s,∑y∈t, f x y):=
    by rewrite [(Sum_insert_of_not_mem _ H)]

  -- originally l12 in m14.lean
  lemma exSum_aux3 (H: a∉ s): (∑ y∈t,∑x∈(insert a s), f x y)= 
  ∑ y∈t,(f a y + ∑ x∈s, f x y) :=
  Sum_ext (take y, assume h, by rewrite (Sum_insert_of_not_mem _ H))
  
  -- originally t4 in m14.lean
  theorem Sum_exchange : 
  (∑ x∈s,∑ y∈t, f x y) = ∑ y∈t, ∑ x∈s, f x y := 
    finset.induction_on s exSum_aux1 (λ a s0 nin h,
    by rewrite[(exSum_aux2 nin),(exSum_aux3 nin),Sum_add,h] )

  /- Sum can have curried/uncurried form -/

  
  -- originally t1 in m14.lean
  lemma Sum_uncurry_singleton: 
  (∑ x ∈ '{a}, ∑ y ∈ '{b}, f x y )= ∑ z ∈ '{a}*'{b}, (uncurry f) z :=
    by rewrite [(Sum_singleton a _)]
  
  -- originally curry_l1 in m14.lean
  lemma Sum_uncurry_empty_left: 
  (∑ x∈∅*t, (uncurry f) x) = ∑ x∈∅,∑ y∈t, f x y :=
    by rewrite [(empty_product t), Sum_empty]

  -- originally subgoal2 in m14.lean
  lemma Sum_uncurry_empty_right : 
  (∑x∈s*∅, (uncurry f) x) = ∑ x∈s,∑y∈∅, f x y :=
    by rewrite [product_empty,Sum_empty,Sum_zero]

  -- originally sup1 in m14.lean
  lemma Sum_uncurry_aux1 (h: t∩t₁ = ∅):(∑ x∈s*(t∪t₁), (uncurry f) x) = 
  (∑ x∈s*t, (uncurry f) x) + (∑ x∈s*t₁, (uncurry f ) x):=
  by rewrite [product.union_right_distrib,
  (Sum_union _ (product.disjoint_of_disjoint_right h))]

  -- originally sup2 in m14.lean
  lemma Sum_uncurry_aux2 (h:t∩t₁ = ∅): (∑x∈s, ∑y∈t∪t₁, f x y) = 
  ∑ x∈s, (∑ y∈t, f x y) + (∑y∈t₁, f x y) :=
    Sum_ext (take x, assume hx, by rewrite (Sum_union _ h))

  -- originally sup3 in m14.lean
  lemma Sum_uncurry_aux3 (h:t∩t₁ = ∅):
  (∑ x∈s, (∑ y∈t, f x y) + (∑y∈t₁, f x y)) = 
  (∑ x∈s,∑y∈t, f x y) + ∑ x∈s, ∑y∈t₁, f x y :=
  by rewrite Sum_add

  -- originally subgoal1 in m14.lean
  lemma Sum_uncurry_aux4 : (∑ x∈'{a}*t, (uncurry f) x) = 
  ∑ x∈'{a},∑y∈t, f x y := 
  finset.induction_on t Sum_uncurry_empty_right (λ x t0 xnin h,
  have h1:'{x}∩t0 = ∅, from singleton_inter_of_not_mem xnin,
  by rewrite [(insert_eq x t0),(Sum_uncurry_aux2 h1),(Sum_uncurry_aux1 h1),
  (Sum_uncurry_aux3 h1),h,Sum_uncurry_singleton])

  -- originally sup4 in m14.lean
  lemma Sum_uncurry_aux5 (h:s∩s₁ = ∅): (∑ x∈(s∪s₁)*t, (uncurry f) x) =
  (∑ x∈s*t,(uncurry f) x) + (∑x∈s₁*t,(uncurry f) x) :=
    by rewrite [product.union_left_distrib,
    (Sum_union _ (product.disjoint_of_disjoint_left h))]
  
  -- originally sup5 in m14.lean
  lemma Sum_uncurry_aux6 (h:s∩s₁ = ∅): (∑ x∈s∪s₁, ∑y∈t, f x y) = 
  (∑ x∈s, ∑ y∈t, f x y) + (∑x∈s₁, ∑y∈t, f x y) :=
    by rewrite (Sum_union _ h)
  
  -- origianlly final_goal in m14.lean
  theorem Sum_uncurry : (∑ x∈s*t, (uncurry f) x) = 
  ∑ x∈s, ∑ y∈t, f x y := 
  finset.induction_on s Sum_uncurry_empty_left (λu s0 unin h, 
  have '{u}∩s0 = ∅, from singleton_inter_of_not_mem unin,
  by rewrite [(insert_eq u s0),(Sum_uncurry_aux5 this),
  (Sum_uncurry_aux6 this),Sum_uncurry_aux4,h])

  theorem Sum_curry : (∑ x∈s*t, f' x) = ∑x∈s, ∑y∈t, (curry f') x y :=
    by rewrite [-(uncurry_curry f'),Sum_uncurry]

end finset


namespace set
  
  variables {s s₁: set A}{t:set B}[fins : finite s][fint: finite t]
  variables {g:A -> B -> C}{k: A -> C}
  
  section
  
  open [notation]finset

  include fins fint c

  lemma exSum_aux1 : (∑ x∈s, ∑y∈ t, f x y) = 
  ∑ x∈ (to_finset s), ∑y∈(to_finset t), f x y :=
  by rewrite Sum_def

  lemma exSum_aux2 : (∑ y∈t, ∑ x∈s, f x y) = 
  ∑ y∈(to_finset t), ∑x∈(to_finset s), f x y :=
  by rewrite Sum_def

  include deceqA deceqB
  theorem Sum_exchange : (∑ x∈ s, ∑y∈ t,f x y) = 
  ∑ x∈t, ∑ y∈s, f y x := 
  by rewrite [exSum_aux1,exSum_aux2,finset.Sum_exchange]

  lemma Sum_uncurry_aux1 :(∑ x∈s*t, (uncurry f) x) = 
  ∑ x∈(to_finset s)*(to_finset t), (uncurry f) x := 
    have finite (product s t), from !finite_product,
    by rewrite [Sum_def,to_finset_product]

  lemma Sum_uncurry_aux2 : (∑ x∈s,∑y∈t, f x y) = 
  ∑ x∈(to_finset s),∑ y∈(to_finset t), f x y:=
    by rewrite Sum_def

  theorem Sum_uncurry:(∑ x∈ s*t, (uncurry f) x) = ∑ x∈s,∑y∈t, f x y:= 
    by rewrite [Sum_uncurry_aux1, Sum_uncurry_aux2, finset.Sum_uncurry]

  theorem Sum_curry: (∑ x∈ s*t, f' x) = ∑x∈s,∑y∈t, (curry f') x y :=
    by rewrite [-(uncurry_curry f'),Sum_uncurry]  
  

  theorem eq_sum_of_eq_fun (h:∀ x y, f x y = g x y): 
  (∑ x∈s,∑y∈t, f x y)=∑x∈s,∑y∈t, g x y := 
    have f = g, from funext (λx, funext (λ y, h x y)),
    by rewrite this

  end

  /- Properties of reduced set of Sum: originally in m15.lean -/
  section
  
    open classical
  
    include c
    
    lemma eq_zero_of_inter_empty(h: s∩s₁ = ∅):
    (∑x∈s, (ite (s₁ x) 1 0)*(k x)) = ∑ x∈s, (0:C) :=
      Sum_ext(λ x hin, have x∉s₁, from
      proof suppose x∈s₁, show false, by rewrite [-(mem_empty_eq x),-h];
      apply mem_inter hin this qed,
      have (ite (s₁ x) (1:C) 0) = 0, from if_neg this,
      by rewrite [this];simp)

    include fins
    lemma Sum_reduced_aux1:(∑x∈s, k x)=(∑x∈s∩s₁,k x)+∑x∈s\s₁, k x :=
      have finite (s∩s₁), from finite_subset (inter_subset_left s s₁),
      have finite (s\s₁), from finite_subset (diff_subset s s₁),
      have (s∩s₁)∩(s\s₁)=∅, from inter_inter_diff_empty,
      by rewrite [(@inter_union_diff_cancel A s₁ s)at{1},(Sum_union _ this)]
    
    omit fins
    lemma Sum_reduced_aux2(h:s⊆s₁):
    (∑x∈s,(ite (s₁ x) 1 0)*(k x)) = ∑x∈s, k x :=
      Sum_ext(λ x hin, have x∈s₁, from mem_of_subset_of_mem h hin,
      have (ite (s₁ x) (1:C) 0) = 1, from if_pos this,
      by rewrite [this];apply semiring.one_mul)
    
    include fins
    theorem Sum_reduced: (∑x∈s, (ite (s₁ x) 1 0)*(k x))=∑x∈s∩s₁, k x :=
      by rewrite [(@Sum_reduced_aux1 A C _ s s₁ _ _),
   (eq_zero_of_inter_empty (@diff_inter_self_empty A s₁ s)), Sum_zero, 
   (Sum_reduced_aux2 (inter_subset_right s s₁))];apply semiring.add_zero
  
    theorem Sum_reduced_flex (h:∀x, x∈s\s₁ -> k x = 0):
    (∑x∈s, k x) = ∑x∈s∩s₁, k x :=
      have (∑x∈s\s₁, k x) =∑x∈s\s₁, 0, 
        by apply Sum_ext;intro x hx; apply (h x hx),
      have (∑x∈s\s₁, k x) = 0, by rewrite [this,Sum_zero],
      by rewrite [(@Sum_reduced_aux1 A C _ s s₁ _ _),this];simp
    
    check @Sum_reduced_flex
  end
  
end set
