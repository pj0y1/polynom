/- 
finset product and set product
some theorems with ' denoting prod version, for convenience

some disjoint properties of set, orginally in m15.lean
-/

import data.set data.finset.comb
import algebra.group_bigops
open set classical prod.ops

variables {A B:Type}{a:A}{b:B}{x:A×B}

namespace set
  
  definition product (s: set A)(t: set B) : set (A × B) := 
    λ x, x.1 ∈ s ∧ x.2 ∈ t
  notation a * b := product a b

end set

namespace finset
  open [notation]set

  variables {s s1:finset A}{t t1: finset B}

  theorem mem_product_iff: ((a,b)∈s*t) ↔ (a∈s∧b∈t) := 
    iff.intro 
    (λl,and.intro(mem_of_mem_product_left l)(mem_of_mem_product_right l)) 
    (λr,mem_product (and.left r)(and.right r))

  theorem mem_product_iff': x∈s*t ↔ x.1∈s∧x.2∈t := 
    match x with (m, n) := !mem_product_iff end

  theorem mem_product_eq: ((a,b)∈s*t) = (a∈s∧b∈t) := 
    propext (!mem_product_iff)

  theorem mem_product_eq': x∈s*t = (x.1∈s∧x.2∈t):=
    match x with (a,b) := propext (!mem_product_iff) end

  theorem mem_to_set_product: ((a,b)∈s*t) = (a∈to_set s∧b∈to_set t):=
    !mem_product_eq

  theorem mem_to_set_product': x∈ s*t = (x.1∈to_set s∧x.2∈to_set t):=
    match x with (a,b) := !mem_product_eq end

  theorem to_set_product': to_set (s*t) = (to_set s)*(to_set t) := 
    funext (λ x, match x with (a,b) := !mem_to_set_product end)

  /-finset product singleton, originally in m14.lean-/
  theorem singleton_of_singleton_product:'{a}*'{b} = '{(a,b)} := 
    ext (take x, match x with (u,v) := iff.intro
    (assume l, 
      have hu:u ∈ '{a}, from mem_of_mem_product_left l,
      have hv:v ∈ '{b}, from mem_of_mem_product_right l,
      mem_product hu hv)
    (assume r, 
      have H:(u,v) = (a,b), from eq_of_mem_singleton r,
      have (u,v).1 = (a,b).1, by rewrite H,
      have u = a, from this,
      have hu: u ∈ '{a}, from mem_singleton_of_eq this,
      have (u,v).2 = (a,b).2, by rewrite H,
      have v = b, from this,
      have hv: v ∈ '{b}, from mem_singleton_of_eq this,
      mem_product hu hv)
    end)


 namespace product --originally defined in m13.lean
    
    variables [deceqA : decidable_eq A][deceqB: decidable_eq B]

    local attribute prod.has_decidable_eq [instance]
  
    /- Union distribution-/
    include deceqA deceqB

    theorem union_right_distrib : s*( t1 ∪ t) = s*t1 ∪ s*t :=
    ext (take x, match x with (u,v) := iff.intro
    (assume l, have u∈s∧v∈(t1∪t), by rewrite -mem_product_eq;exact l,
      have hu: u ∈ s, from and.left this,
      have hv: v ∈ t1 ∨ v ∈ t, 
      by rewrite -mem_union_eq;apply and.right this,
      or.elim hv (assume h, mem_union_l (mem_product hu h)) 
      (assume h, mem_union_r (mem_product hu h)))
    (assume r, have (u,v)∈ s*t1∨(u,v)∈s*t, 
      by rewrite -mem_union_eq;exact r,
      or.elim this 
      (assume h, have hu:u ∈s, from mem_of_mem_product_left h,
      have v ∈ t1, from mem_of_mem_product_right h,
      have hv: v∈ t1∪t, from mem_union_l this,
      mem_product hu hv) 
      (assume h, have hu:u ∈s, from mem_of_mem_product_left h,
      have v ∈ t, from mem_of_mem_product_right h,
      have hv:v ∈t1∪t, from mem_union_r this,
      mem_product hu hv))
    end) 


 -- corollary c1:'{a}*(insert b t) = '{a}*'{b} ∪ '{a}*t := 
   -- by rewrite {insert b t}insert_eq; apply union_right_distrib

  theorem union_left_distrib: (s∪s1)*t = s*t ∪ s1*t :=
    ext ( take x, match x with (u,v) := iff.intro
    (assume l, 
      have hu: u∈s∨u∈s1, by rewrite -mem_union_eq;
      apply mem_of_mem_product_left l,
      have hv: v∈t, from mem_of_mem_product_right l,
      or.elim hu
      (assume h, mem_union_l (mem_product h hv))
      (assume h, mem_union_r (mem_product h hv)))
    (assume r,
      have (u,v)∈s*t∨(u,v)∈s1*t, 
      by rewrite -mem_union_eq;exact r,
      or.elim this
      (assume h, have u∈s, from mem_of_mem_product_left h,
      have hu:u∈s∪s1, from mem_union_l this,
      have hv: v∈t, from mem_of_mem_product_right h,
      mem_product hu hv)
      (assume h, have u∈s1, from mem_of_mem_product_left h,
      have hu: u∈s∪s1, from mem_union_r this,
      have hv: v∈t, from mem_of_mem_product_right h,
      mem_product hu hv))
    end)
    
  --corollary c2:(insert a s)*'{b} = '{a}*'{b} ∪ s*'{b} := 
    --by rewrite {insert a s}insert_eq; apply union_left_distrib

 -- lemma l1:(insert a s)*(insert b t) = '{a}*(insert b t)∪ s*(insert b t):=
   -- by rewrite {insert a s}insert_eq; apply union_left_distrib

  --lemma l2:'{a}*(insert b t)∪ s*(insert b t)='{a}*'{b}∪'{a}*t∪s*(insert b t):=
    --by rewrite [{insert b t}insert_eq, *union_right_distrib]

  --theorem t3: (insert a s)*(insert b t)= '{a}*'{b}∪'{a}*t∪ s*'{b}∪s*t := 
    --by rewrite [l1,l2,{insert b t}insert_eq, *union_right_distrib,*union_assoc]


/-Jul 11: finished finset product union distribution-/

  /-NEXT: disjointness!-/

  theorem disjoint_of_disjoint_left (H: s∩s1=∅):(s*t) ∩ (s1*t) = ∅ := 
    by_contradiction 
    ( assume h: ¬ ((s*t) ∩ (s1*t) = ∅),
    have (s*t) ∩ (s1*t) ≠ ∅, from h,
    show false, from
    (exists.elim (exists_mem_of_ne_empty this)
    (λ (x:A×B) (hx: x∈ (s*t) ∩ (s1*t)), 
    have h1: x∈s*t, from mem_of_mem_inter_left hx,
    have h2: x∈s1*t,from mem_of_mem_inter_right hx,
    have h3: x.1∈s, from and.left ((iff.mp mem_product_iff') h1),
    have h4: x.1∈s1, from and.left ((iff.mp mem_product_iff') h2),
    have x.1∈s∩s1,from mem_inter h3 h4,
    have x.1∈∅, by rewrite [H at this];exact this,
    show false, by rewrite [mem_empty_eq at this];exact this)))

    --corollary c3(H:a∉s):('{a}*t) ∩ (s*t) = ∅ :=
      --by apply l3; apply singleton_inter_of_not_mem H

    theorem disjoint_of_disjoint_right (H: t∩t1 = ∅):(s*t)∩(s*t1) = ∅:=
      by_contradiction
      ( assume h: ¬ ((s*t) ∩ (s*t1) = ∅),
      have (s*t) ∩ (s*t1) ≠ ∅, from h,
      show false, from
      (exists.elim (exists_mem_of_ne_empty this)
      (λ (x:A×B) (hx: x∈ (s*t) ∩ (s*t1)), 
      have h1: x∈s*t, from mem_of_mem_inter_left hx,
      have h2: x∈s*t1,from mem_of_mem_inter_right hx,
      have h3: x.2∈t, from and.right ((iff.mp mem_product_iff') h1),
      have h4: x.2∈t1, from and.right ((iff.mp mem_product_iff') h2),
      have x.2∈t∩t1,from mem_inter h3 h4,
      have x.1∈∅, by rewrite [H at this];exact this,
      show false, by rewrite [mem_empty_eq at this];exact this)))

    --corollary c4(H:b∉t):(s*'{b})∩(s*t) =∅ :=
      --by apply l4;apply singleton_inter_of_not_mem H

  end product

end finset

namespace set
  
  variables {s s₁:set A}{t: set B}

  theorem finite_product[instance][finite s][finite t]:finite (s*t):=
    exists.intro (#finset to_finset s * to_finset t) 
    (by rewrite [finset.to_set_product',*to_set_to_finset])

  theorem mem_product: a ∈ s → b ∈ t → (a, b) ∈ s*t :=
    λ p q, and.intro p q

  theorem mem_of_mem_product_left: (a,b) ∈ s*t → a ∈ s :=
    λ p, and.left p
  
  theorem mem_of_mem_product_left': x∈ s*t -> x.1∈s :=
    λ p, and.left p

  theorem mem_of_mem_product_right: (a,b) ∈ s*t  → b ∈t :=
    λ p, and.right p

  theorem mem_of_mem_product_right': x∈ s*t -> x.2∈t :=
    λ p, and.right p

  theorem empty_product : @empty A * t = ∅ :=
    by_contradiction (assume h: ¬ @empty A * t = ∅,
    have @empty A * t ≠ ∅, from h, show false, from
    obtain (x:A×B)(hx: x∈@empty A * t), from exists_mem_of_ne_empty this,
    have x.1 ∈ @empty A, from mem_of_mem_product_left' hx,
    by rewrite [(mem_empty_eq x.1) at this];exact this)

  theorem product_empty : s * @empty B = ∅ :=
    by_contradiction (assume h: ¬ s * @empty B = ∅,
    have s * @empty B ≠ ∅, from h, show false, from
    obtain (x:A×B)(hx: x∈s * @empty B), from exists_mem_of_ne_empty this,
    have x.2 ∈ @empty B, from mem_of_mem_product_right' hx,
    by rewrite [(mem_empty_eq x.2) at this];exact this)

  theorem mem_product_iff: ((a,b) ∈ s*t) ↔ (a ∈ s ∧ b ∈ t) := 
    iff.intro 
    (λ H,and.intro (mem_of_mem_product_left H) (mem_of_mem_product_right H)) 
    (λ H', mem_product (and.left H') (and.right H'))

  theorem mem_product_iff': x ∈ s*t ↔ x.1 ∈ s ∧ x.2 ∈ t := 
    match x with (m, n) := !mem_product_iff end

  theorem mem_product_eq: ((a,b) ∈ s * t) = (a ∈ s ∧ b ∈ t) := 
    propext (!mem_product_iff)

  theorem mem_product_eq': x∈ s*t = (x.1 ∈s ∧ x.2 ∈ t):=
    propext (!mem_product_iff')

  open [notation] finset

  theorem mem_to_finset_product_left [finite s](h:(a,b)∈ s*t): 
  a∈to_finset s :=
    by rewrite [(mem_to_finset_eq a s)];apply (mem_of_mem_product_left h)

  theorem mem_to_finset_product_right [finite t](h:(a,b)∈ s*t):
  b∈ to_finset t :=
    by rewrite [(mem_to_finset_eq b t)];apply (mem_of_mem_product_right h)

  theorem mem_product_of_mem_to_finset [finite s][finite t]
  (h1: a∈ to_finset s)(h2: b ∈ to_finset t):(a,b)∈s*t :=
    by rewrite [(mem_to_finset_eq b t) at h2, (mem_to_finset_eq a s) at h1]; 
    apply mem_product h1 h2

  theorem mem_to_finset_product [finite s][finite t]: 
  ((a,b) ∈ s * t) = (a ∈ to_finset s ∧ b ∈ to_finset t) := 
    propext (iff.intro (assume l, and.intro (mem_to_finset_product_left l) 
    (mem_to_finset_product_right l)) 
    (assume r, mem_product_of_mem_to_finset (and.left r) (and.right r)))

  theorem mem_to_finset_product' [finite s] [finite t]: 
  x∈ s*t = (x.1 ∈ to_finset s ∧ x.2 ∈ to_finset t) := 
    match x with (a,b) := !mem_to_finset_product end

  theorem to_finset_product [finite s][finite t]: 
  to_finset (s * t) = finset.product (to_finset s) (to_finset t) := 
    have h:finite (s*t), from finite_product,
    finset.ext (λ x, iff.intro 
    (assume l, have x∈s*t, 
      by rewrite [(mem_to_finset_eq x (s*t)) at l];exact l,
    have x.1 ∈ to_finset s ∧ x.2 ∈ to_finset t, 
      by rewrite [mem_to_finset_product' at this];exact this,
    show x∈(to_finset s)*(to_finset t), 
      by rewrite [-finset.mem_product_eq' at this];exact this) 
    (assume r, 
    have x∈ s*t,
      by rewrite [finset.mem_product_eq' at r,-mem_to_finset_product' at r];
      exact r,
    show x∈ to_finset (s*t), 
      by rewrite (mem_to_finset_eq x (s*t));exact this))

  /-disjoint and inter-/
  
  theorem inter_union_diff_cancel: s₁ = (s₁∩s) ∪ (s₁\s) :=
    ext (take x, iff.intro 
    (assume l, or.elim (em (x∈s)) 
      (assume h, mem_unionl (mem_inter l h)) 
      (assume h, mem_unionr (mem_diff l h)))
    (assume r, or.elim r
      (assume h, mem_of_mem_inter_left h)
      (assume h, mem_of_mem_diff h))) 


  theorem inter_inter_diff_empty: (s₁∩s) ∩ (s₁\s) = ∅ :=
    by_contradiction (assume h: (s₁∩s)∩(s₁\s) ≠ ∅, 
    obtain (x:A)(hx: x∈(s₁∩s)∩(s₁\s)), from exists_mem_of_ne_empty h,
    have x∈(s₁∩s)∧x∈(s₁\s), by rewrite [mem_inter_eq at hx];exact hx,
    have x∈s, from mem_of_mem_inter_right (and.left this),
    have hn: x∉s, from not_mem_of_mem_diff (and.right hx),
    show false, from absurd this hn)

  theorem diff_inter_self_empty: (s₁\s)∩s = ∅ :=
    by rewrite [(diff_eq s₁ s),inter_assoc,compl_inter_self,inter_empty]

  theorem subset_inter_eq_self (h:s⊆s₁): s₁∩s = s :=
    have s⊆s, from λx h, h,
    have h1:s⊆s₁∩s, from subset_inter h this,
    have h2:s₁∩s⊆s, from inter_subset_right s₁ s,
    subset.antisymm  h2 h1

  /- image and preimage -/
  
  theorem empty_preimage_of_empty_image {f:A -> B}(h:t=∅):
  f '- t = ∅ :=
    by_contradiction assume hne,
    have f '- t ≠ ∅, from hne,
    obtain (a:A)(ha: a∈ f '- t), from exists_mem_of_ne_empty this,
    have f a ∈ t, from mem_of_mem_preimage ha,
    have t≠∅, from ne_empty_of_mem this,
    absurd h this

  theorem empty_of_empty_image {f:A -> B}(h: f ' s = ∅):
    s = ∅ :=
    by_contradiction assume hne,
    have s≠∅, from hne,
    obtain (a:A)(ha: a∈s), from exists_mem_of_ne_empty this,
    have f a ∈ f ' s, from mem_image_of_mem f ha,
    have f ' s ≠ ∅, from ne_empty_of_mem this,
    absurd h this

  theorem exists_mem_of_mem_image {f:A->B}(h:b∈ f ' s):
   ∃a,a∈s∧f a = b := h

  /- singleton -/
    
  theorem eq_singleton_iff_all_eq (h: ∀x:A, x∈s ↔ x = a): s = '{a} :=
  ext (take x, iff.intro
  (assume l, mem_singleton_of_eq (iff.mp (h x) l))
  (assume r, have heq:x=a, from eq_of_mem_singleton r,
  iff.mpr (h x) heq))

  theorem singleton_of_all_eq_of_ne_empty(h: ∀x:A, x∈s -> x = a)(g: s≠∅): 
  s = '{a}:= 
  ext (take x, iff.intro
  (assume l, mem_singleton_of_eq (h x l))
  (assume r, have heq:x=a, from eq_of_mem_singleton r,
  obtain (u:A)(hu:u∈s), from exists_mem_of_ne_empty g,
  have u=a, from h u hu, show x∈s, by rewrite [heq,-this];exact hu))
  

  theorem empty_or_singleton_of_inter_singleton: s∩'{a} = ∅ ∨ s∩'{a} = '{a} :=
  or.elim (em (s∩'{a} = ∅))
  (λh, or.inl h)
  (λh,have h1: s∩'{a}⊆'{a}, from inter_subset_right s '{a}, 
    have h2:s∩'{a}≠∅, from h,
    or.inr (singleton_of_all_eq_of_ne_empty 
    (λx hx, have x∈'{a}, from mem_of_subset_of_mem h1 hx,
    show x=a, from eq_of_mem_singleton this) h2))


  /- singleton image -/
  theorem singleton_image {f:A-> B}(h: f ' s = '{b}):
  ∀x, x∈s -> f x = b :=
  λ x hs, have f x ∈ f ' s, from mem_image_of_mem f hs,
  have f x ∈ '{b}, by rewrite h at this;exact this,
  show f x = b, from eq_of_mem_singleton this

  theorem singleton_image' {f:A->B}(h: f ' s = '{b}):
  ∀x, x∈s -> b = f x :=
  λ x hs, eq.symm (singleton_image h x hs)
end set
