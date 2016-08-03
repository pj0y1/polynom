import finsupp alg_aux
open classical set prod.ops eq.ops
open function comm_cancel_monoid

set_option max_memory 2048

namespace function_aux

variables {A B:Type}

section commutativity --1
 
  variables [comm_semigroup A][comm_semiring B]

  /- for polynoms to be commutative, B has to be comm_ring-/
  theorem mul_comm (f g: A -> B)[finite (supp f)][finite (supp g)]:
  mul f g = mul g f := 
    funext (λa, by rewrite [↑function.mul,Sum_exchange];
    apply Sum_ext;intro x hx;apply Sum_ext;intro y hy;simp)

  -- thus in sum.lean eq_sum_of_eq_fun obsoleted

end commutativity


section assoc --2

  open eq.ops
  variables [comm_cancel_monoid A][semiring B]
  variables (f g k:A -> B)(m n: A)
  variables [finite (supp f)][finite (supp g)][finite (supp k)]

  section --assoc_from_right_aux

  variables {C:Type}{p: C -> Prop}
  
  theorem ite_exchange {c:C}(u v:B):
    (ite (p c) (1:B) 0)*(u * v) = u * ((ite (p c) (1:B) 0) * v) :=
  or.elim (em (p c))
  (λh, by rewrite (if_pos h);simp)
  (λh, by rewrite (if_neg h);simp)

  theorem ite_exchange_Sum1{s: set C}{u:B}{v:C-> B}:
    (∑x∈s, (ite (p x) (1:B) 0)*(u * v x)) = ∑x∈s,u * ((ite (p x) (1:B) 0) * v x) :=
  Sum_ext(λx hx,
  or.elim (em (p x))
  (λh, by rewrite (if_pos h);simp)
  (λh, by rewrite (if_neg h);simp))

  theorem ite_exchange_Sum2 {q: C -> C -> Prop}{s t: set C}{u:B}{v w:C -> B}:
   (∑x∈s, ∑y∈t, (ite (q x y) 1 0)*(u *(v x * w y))) =
   ∑x∈s, ∑y∈t, u*((ite (q x y) 1 0)*(v x * w y)):=
  Sum_ext (λx hx, Sum_ext (λy hy,  or.elim (em (q x y))
  (λh, by rewrite (if_pos h);simp)
  (λh, by rewrite (if_neg h);simp)))

  theorem mul_Sum2 {s t: set C}{u:B}{f:C-> C-> B}:
   (∑x∈s,∑y∈t, u * f x y) = u*(∑x∈s,∑y∈t, f x y) :=
  by rewrite (semiring.mul_Sum _);apply Sum_ext;intros x hx;
     rewrite (semiring.mul_Sum _)
  end 

  lemma assoc_aux1_aux {s: set A}[finite s]{fx gx: A-> B}:
    (∑x∈s\supp gx, (fx x)*(gx x)) = ∑x∈s\supp gx, 0 :=
    Sum_ext (λx h, have x∉supp gx, from not_mem_of_mem_diff h,
     by rewrite [-(eq_zero_eq_not_mem_supp gx x) at this,this];
        apply semiring.mul_zero)

  theorem assoc_aux1 {t:A -> B}: (∑x∈supp(mul f g),(t x)*(mul f g x))=
  ∑x∈img f g, (t x)*(mul f g x) :=
    have finite(img f g), from !finite_img,
    have h:supp (mul f g)⊆ img f g, from mul_supp_subset_img f g,
    by rewrite [(@Sum_reduced_aux1 _ _ _ (img f g) (supp (mul f g)) _ _),
    (subset_inter_eq_self h),assoc_aux1_aux,Sum_zero];simp

  lemma assoc_aux2_aux:
  preimage (uncurry mul) (λx:A, m = n * x) = (λx:A×A, m = n* (x.1 * x.2)) :=
  ext (λt, iff.intro
  (λl, have (uncurry mul) t ∈ (λx:A, m = mul n x), 
    from (mem_of_mem_preimage l),
    have h1:m = n* (uncurry mul t), from this,
      have uncurry mul t = t.1 * t.2, from proof
      match t with (a,b) := rfl end qed,
    have m = n* (t.1 * t.2), by rewrite [-this,h1],
    show (λx:A×A, m = n * (x.1 * x.2)) t, from this)
  (λr, have h1: m = n * (t.1 * t.2), from r,
     have t.1 * t.2 = uncurry mul t, from proof
     match t with (a,b) :=  rfl end qed,
    have m = n * (uncurry mul t), by rewrite [-this, h1],
    have uncurry mul t ∈ (λx:A, m = n * x), from this,
    mem_preimage this))

  lemma equiv_pred_curry : (λx:A×A,m = (x.1*x.2)*n) = (λx:A×A, m =n*(x.1*x.2)) :=
    ext (λx, iff.intro 
    (λ l, have m = (x.1*x.2)*n, from l,
      show x∈(λx, m = n*(x.1*x.2)), 
      from eq.trans this (comm_cancel_monoid.mul_comm (x.1*x.2) n))
    (λ r, have m = n* (x.1 *x.2), from r,
      show x∈(λx, m = (x.1*x.2)*n),
      from eq.trans this (comm_cancel_monoid.mul_comm n (x.1*x.2)))
    )

  
  theorem assoc_aux2:
  (img f g)∩(λx, m=n*x) =
  image (uncurry mul) (supp f * supp g ∩ (λx,m=n*(x.1*x.2))):=  
    by rewrite [-(assoc_aux2_aux m n)];apply image_inter

  
  corollary assoc_aux2_cor1: -- originally lem6 in nind.lean
  (img f g)∩(λx, m=n*x) = ∅ ↔ 
  (supp f * supp g ∩ (λx,m=n*(x.1*x.2))) = ∅ :=
    iff.intro
    (λl, by rewrite [(assoc_aux2 f g m n) at l];
         apply (empty_of_empty_image l))
    (λr, by rewrite [(assoc_aux2 f g m n),r,image_empty])


  corollary assoc_aux2_cor2: -- lem8 in nind.lean
   (img f g)∩(λx,m=n*x) ≠ ∅ -> ∃ u:A, 
    (img f g)∩(λx,m=n*x) = '{u} ∧
    ∀v:A×A, v∈supp f*supp g∩(λp,m=n*(p.1*p.2)) ->
      u = v.1*v.2 :=
    λh, obtain (u:A)(hu: u∈(img f g)∩(λx,m=n*x)), 
    from exists_mem_of_ne_empty h,
    have h1: u∈(λx,m=n*x), from and.right hu,
    have h2:(λx,m=n*x) = '{u}, from proof
      or.elim (empty_or_singleton_right m n)
      (λh, absurd h (ne_empty_of_mem h1))
      (λh, obtain (v:A)(hv:(λx,m=n*x)='{v}), from h,
      have u = v, from eq_of_mem_singleton (hv ▸ h1),
      by rewrite [-this at hv];exact hv) qed,
    have h3:(img f g)∩(λx,m=n*x) = '{u}, from proof
      have (img f g)∩'{u} = '{u}, from
      or.elim (@empty_or_singleton_of_inter_singleton _ u (img f g))
      (λh, absurd h (ne_empty_of_mem (h2 ▸ hu))) (λh, h), 
      h2⁻¹ ▸ this qed,
    have h4:(λx:A×A, uncurry mul x) = (λx, x.1 * x.2), from 
    funext (λx, match x with (a,b) := rfl end),
    have ∀v:A×A, v∈(supp f * supp g)∩(λx,m=n*(x.1*x.2))-> u= v.1 * v.2, 
    by apply singleton_image';rewrite [-h4,-(assoc_aux2 f g m n),h3],
    exists.intro u (and.intro h3 this)

 
 
  lemma assoc_aux3_aux {u:A}(h:m=n*u):
  (λx,m=n*(x.1*x.2)) = (λx,u=x.1*x.2) :=
  ext (λ x, iff.intro
  (λl, have m=n*(x.1*x.2), from l,
    have n*u = n*(x.1 * x.2), from h ▸ this,
    comm_cancel_monoid.mul_left_cancel _ _ _ this)
  (λr, have u=x.1*x.2, from r,
    show m=n*(x.1*x.2), by rewrite [-this,h]))
 


  theorem assoc_aux3_right:
  (∑x∈(img f g)∩(λx,m=n*x), mul f g x) =
  ∑x∈supp f * supp g ∩(λx, m=n*(x.1*x.2)), (f x.1)*(g x.2) :=
    have finite (supp f * supp g), from finite_product,
    or.elim (em (img f g ∩ (λx:A, m = n*x) = ∅) )
    (λ he, by rewrite [he,(iff.mp (assoc_aux2_cor1 f g m n) he),*Sum_empty])
    (λ hne,obtain (u:A) hu, from assoc_aux2_cor2 _ _ _ _ hne,
      have h1:m = n * u, from proof
        show u∈(λx,m=n*x), 
        from mem_of_mem_inter_right 
        ((and.left hu)⁻¹ ▸ (mem_singleton u)) qed,
      have h2: (λx,(ite (u=x.1*x.2) 1 0)*(f x.1 * g x.2)) = 
        uncurry (λ x y, (ite (u=x * y) 1 0)*(f x * g y)), 
        by rewrite -(uncurry_curry _),
      by rewrite [(and.left hu),Sum_singleton,(assoc_aux3_aux m n h1),
     -Sum_reduced,↑function.mul,h2,-Sum_uncurry])



  theorem assoc_aux3_left:
  (∑x∈(img f g)∩(λx,m=x*n), mul f g x) =
  ∑x∈supp f * supp g ∩(λx, m=(x.1*x.2)*n), (f x.1)*(g x.2) :=
  by rewrite [(equiv_pred m n),(equiv_pred_curry m n)];apply assoc_aux3_right
 
  theorem assoc_aux3_general_right:
  (∑x∈(img f g), (ite (m=n*x) 1 0)*(mul f g x)) =
  ∑x∈supp f * supp g, (ite (m=n*(x.1*x.2)) 1 0)*(f x.1* g x.2) :=
    have finite (img f g), from finite_img f g,
    have finite (supp f * supp g), from finite_product,
    by rewrite [*Sum_reduced,assoc_aux3_right]

  theorem assoc_aux3_general_left:
  (∑x∈(img f g), (ite (m=x*n) 1 0)*(mul f g x)) =
  ∑x∈supp f * supp g, (ite (m=(x.1*x.2)*n) 1 0)*(f x.1* g x.2) :=
    have finite (img f g), from finite_img f g,
    have finite (supp f * supp g), from finite_product,
    by rewrite [*Sum_reduced,assoc_aux3_left]

 
  theorem assoc_from_right:
  (∑x∈supp k, ∑y∈supp(mul f g), (ite (m=x*y) 1 0)*(k x * mul f g y))=
  ∑x∈supp k,∑y∈supp f,∑z∈supp g, (ite (m=x*(y*z)) 1 0)*(k x *(f y * g z)) :=
  Sum_ext (λx hx, 
   let f' := (λt,(ite (m=x*(t.1*t.2)) 1 0)*(f t.1 * g t.2)) in 
   by rewrite [ite_exchange_Sum1, -(semiring.mul_Sum _ (k x)),
   ite_exchange_Sum2,mul_Sum2, assoc_aux1, (assoc_aux3_general_right f g m x), 
   (@Sum_curry _ _ _ _ _ _ f' _ _ _ _)])


/-right direction-/

  theorem assoc_from_left_aux1 :
   (∑x∈supp(mul k f),∑y∈supp g,(ite (m=x*y) 1 0)*(mul k f x * g y)) =
   ∑y∈supp g,(∑x∈supp (mul k f),(ite (m=x*y) 1 0)*(mul k f x)) * g y :=
   have finite (supp (mul k f)), from mul_finite_supp,
   by rewrite [Sum_exchange];apply Sum_ext;intros x hx;
   rewrite (semiring.Sum_mul _);apply Sum_ext;intros y hy;simp

  theorem assoc_from_left_aux2:
  (∑x∈supp (mul k f),(ite (m=x*n) 1 0)*(mul k f x)) =
  ∑x∈supp k,∑y∈supp f, (ite (m=(x*y)*n) 1 0)*(k x * f y):=
   let f' := (λt,(ite (m=(t.1*t.2)*n) 1 0)*(k t.1 * f t.2)) in 
   by rewrite [assoc_aux1,assoc_aux3_general_left,(@Sum_curry _ _ _ _ _ _ f' _ _ _ _)]

  theorem assoc_from_left_aux3:
  (∑y∈supp g,(∑x∈supp (mul k f),(ite (m=x*y) 1 0)*(mul k f x)) * g y)=
  ∑y∈supp g,∑x∈supp k,∑z∈supp f,((ite (m=(x*z)*y) 1 0)*(k x * f z))* g y :=
  Sum_ext (λy hy, by rewrite [assoc_from_left_aux2,(semiring.Sum_mul _)];
  apply Sum_ext; intros x hx;rewrite (semiring.Sum_mul _))

  theorem assoc_from_left_aux4:
  (∑y∈supp g,∑x∈supp k,∑z∈supp f,((ite (m=(x*z)*y) 1 0)*(k x * f z))* g y) = 
  ∑x∈supp k,∑y∈supp g,∑z∈supp f,((ite (m=(x*z)*y) 1 0)*(k x * f z))* g y := 
    by rewrite Sum_exchange

  theorem assoc_from_left_aux5:
  (∑x∈supp k,∑y∈supp g,∑z∈supp f,((ite (m=(x*z)*y) 1 0)*(k x * f z))* g y) =
    ∑x∈supp k,∑z∈supp f,∑y∈supp g,((ite (m=(x*z)*y) 1 0)*(k x * f z))* g y:= 
    by apply Sum_ext; intros x hx; rewrite Sum_exchange
 
  
 theorem assoc_from_left:
 (∑x∈supp(mul k f),∑y∈supp g,(ite (m=x*y) 1 0)*(mul k f x * g y)) =
  ∑x∈supp k,∑y∈supp f,∑z∈supp g, ((ite (m=(x*y)*z) 1 0)*(k x *f y)) * g z :=  
 have finite (supp (mul k f)), from mul_finite_supp,
 (assoc_from_left_aux1 f g k m) ⬝ (assoc_from_left_aux3 f g k m) ⬝ 
 (assoc_from_left_aux4 f g k m) ⬝ (assoc_from_left_aux5 f g k m)

  
  theorem mul_assoc_aux:
  (∑x∈supp k,∑y∈supp f,∑z∈supp g, (ite (m=x*(y*z)) 1 0)*(k x *(f y * g z))) = 
  ∑x∈supp k,∑y∈supp f,∑z∈supp g, ((ite (m=(x*y)*z) 1 0)*(k x *f y)) * g z :=
  Sum_ext (λx hx, Sum_ext (λy hy, Sum_ext (λz hz, by simp)))

  theorem  mul_assoc_aux1 : mul k (mul f g) m =  
  ∑x∈supp k, ∑y∈supp(mul f g), (ite (m=x*y) 1 0)*(k x * mul f g y) := 
    by rewrite [↑mul at {1}]

  theorem mul_assoc_aux2 : mul (mul k f) g m = 
  ∑x∈supp(mul k f),∑y∈supp g,(ite (m=x*y) 1 0)*(mul k f x * g y) :=
    by rewrite [↑mul at {1}]

  theorem mul_assoc : mul (mul f g) k = mul f (mul g k) :=
  funext (λm, (mul_assoc_aux2 g k f m) ⬝ (assoc_from_left g k f m) ⬝ 
  (mul_assoc_aux g k f m)⁻¹ ⬝ (assoc_from_right g k f m)⁻¹ ⬝ (mul_assoc_aux1 g k f m)⁻¹)

end assoc

section one --3
  
  variables [monoid A][semiring B]
  
  variables (f: A -> B)[finite (supp f)](a:A)
  
  -- mul_one and one_mul aux
  theorem singleton_of_one_eq_zero (H:(0:B)=(1:B)): ∀x:B, x=(0:B):=
  λx, show x = (0:B), from
  calc
    x = x * (1:B) : !semiring.mul_one
    ... = x * (0:B) : H
    ... = 0 : !semiring.mul_zero

  lemma singleton_rfl: (λx, a=x) = '{a} :=
  ext (λx,iff.intro 
  (λl, have a = x, from l,
  show x∈'{a}, from mem_singleton_of_eq (eq.symm this))
  (λr, have x=a, from eq_of_mem_singleton r,
  show x∈(λx,a=x), from (eq.symm this)))

  lemma mul_one_aux2 : 
  (∑x∈supp f, (ite (a=x) 1 0)*(f x))= f a :=
  have H:(∑x∈supp f∩'{a}, f x) = f a, from proof
  or.elim (@empty_or_singleton_of_inter_singleton _ a (supp f))
  (λh, have h1:a ∈'{a}, from mem_singleton a,
  have h2: a∉ supp f ∩'{a}, by rewrite h; apply not_mem_empty,
  have h3: a∉ supp f, from not_mem_of_mem_of_not_mem_inter_right h1 h2, 
    by rewrite [-eq_zero_eq_not_mem_supp at h3,h3,h,Sum_empty])
  (λh, by rewrite [h,Sum_singleton]) qed,
  by rewrite [Sum_reduced,(singleton_rfl a),H]


  lemma mul_one_aux1 : (∑y∈supp f, (ite (a=y * 1) 1 0)*(f y * 1)) = 
    ∑y∈supp f, (ite (a=y) 1 0)*(f y):= 
    Sum_ext (λy hy, 
    have h1:f y * 1 = f y, by simp,
    have h2:y * 1 = y, by simp,
    by rewrite [h1,h2])
    
  theorem mul_one : mul f (@one A B _ _) = f :=
  funext (λ a, or.elim (em ((0:B) = (1:B)))
  (λhe, have h1:f a = (0:B), from singleton_of_one_eq_zero he (f a),
    have h2:mul f one a = (0:B), from singleton_of_one_eq_zero he _,
    by rewrite [h2,h1])
  (λhne, have H:(0:B)≠(1:B), from hne,
  have finite (supp (@one A B _ _)), from one_finite_supp,
  have one (1:A) = (1:B), from if_pos rfl,
  by rewrite [↑function.mul, Sum_exchange, (one_supp_singleton H),
    Sum_singleton,this,(mul_one_aux1 _ _),(mul_one_aux2 _ _)]))

  theorem one_mul_aux :
  (∑y∈ supp f, (ite (a= 1*y) 1 0)*(1 * f y))
  = ∑y∈ supp f, (ite (a=y) 1 0)*(f y) :=
  Sum_ext (λy hy, 
    have h1:1*y = y, by simp,
    have h2: 1* f y = f y,by simp,
    by rewrite [h1,h2])

  theorem one_mul : mul (@one A B _ _) f = f :=
  funext (λa, or.elim (em ((0:B) = (1:B)))
  (λhe, have h1:f a = (0:B), from singleton_of_one_eq_zero he (f a),
  have h2:(mul one f) a = (0:B), from singleton_of_one_eq_zero he (mul one f a),
  by rewrite [-h1 at h2,h2])
  (λhne, have h:(0:B)≠(1:B), from hne,
    have one (1:A) = (1:B), from if_pos rfl,
   by rewrite [↑function.mul,(one_supp_singleton h),Sum_singleton, 
     this,(one_mul_aux _ _),(mul_one_aux2 _ _)] ))

end one

section distrib --4
  variables [has_mul A][semiring B](f g k: A -> B)
  variables [finite (supp f)][finite (supp g)][finite (supp k)]

  lemma mul_distrib_aux{f g: A -> B}: 
    ∀a:A, (f + g) a = f a + g a :=
    λa, rfl

  lemma mul_distrib_left_aux {s: set A}[finite s]{g: A->B}(f:A->B)
  (w:B)(H: supp f ⊆ s):
    (∑x∈s,(g x)*(w * f x)) =∑x∈supp f, (g x)*(w * f x) :=
  have h:∀t,t∈ s\supp f -> (g t)*(w * f t)= 0,
     from proof
       λt ht, have t∉ supp f, from not_mem_of_mem_diff ht,
       have f t = 0, by rewrite eq_zero_eq_not_mem_supp;exact this,
    by rewrite this;simp qed,
  by rewrite [(Sum_reduced_flex h),(subset_inter_eq_self H)]

  
  lemma mul_distrib_left_aux1 {s:set A}{k:A -> B}(f g:A -> B)(w:B):
  (∑x∈s, (k x)*(w * ((f+g) x) )) = 
  ∑x∈s,((k x)*(w * f x) + (k x)*(w * g x)) :=
  Sum_ext (λx h, calc 
 (k x)*(w * ((f + g) x)) = (k x)*(w * (f x + g x)): mul_distrib_aux
   ... = (k x)*((w * f x) + (w * g x)): left_distrib
   ... = (k x)*(w * f x) + (k x)*(w * g x): left_distrib)

  theorem mul_left_distrib :
  mul f (g + k) = (mul f g) + (mul f k) :=
  funext (λm, 
  have finite (supp g ∪ supp k), from !finite_union,
  have h1:supp (g+k) ⊆ supp g ∪ supp k, from add_supp_subset_union,
  have h2:supp g ⊆ supp g ∪ supp k, by apply subset_union_left,
  have h3:supp k ⊆ supp g ∪ supp k, by apply subset_union_right,
  by rewrite [mul_distrib_aux,↑function.mul, -Sum_add];
  apply Sum_ext;intros x hx;
  rewrite [-(mul_distrib_left_aux (g+k) (f x) h1),
 (mul_distrib_left_aux1 g k (f x)),Sum_add,
 (mul_distrib_left_aux g (f x) h2),
 (mul_distrib_left_aux k (f x) h3)])

  lemma mul_distrib_right_aux {s: set A}[finite s]{g: A->B}(f:A->B)
  (w:B)(H: supp f ⊆ s):
    (∑x∈s,(g x)*(f x * w)) =∑x∈supp f, (g x)*(f x * w) :=
  have h:∀t,t∈ s\supp f -> (g t)*(f t * w)= 0,
     from proof
       λt ht, have t∉ supp f, from not_mem_of_mem_diff ht,
       have f t = 0, by rewrite eq_zero_eq_not_mem_supp;exact this,
    by rewrite this;simp qed,
  by rewrite [(Sum_reduced_flex h),(subset_inter_eq_self H)]

  lemma mul_distrib_right_aux2 (s t: set A)[finite s]{g: A -> A->B}(f k:A->B)
  (H: supp f ⊆ s):
    (∑y∈t,∑x∈s,(g y x)*(f x * k y)) =∑y∈t,∑x∈supp f, (g y x)*(f x * k y) :=
    Sum_ext (λy hy,mul_distrib_right_aux f (k y) H)
 
  
  lemma mul_distrib_right_aux1 {s:set A}{k:A-> B}(f g:A -> B)(w:B):
  (∑x∈s, (k x)*(((f+g) x) * w )) = 
  ∑x∈s,((k x)*(f x * w) + (k x)*(g x * w)) :=
  Sum_ext (λx h, calc 
 (k x)*( ((f + g) x) * w) = (k x)*((f x + g x) * w): mul_distrib_aux
   ... = (k x)*((f x * w) + (g x) * w): right_distrib
   ... = (k x)*(f x * w) + (k x)*(g x * w): left_distrib)


  theorem mul_right_distrib :
  mul (f + g) k = (mul f k) + (mul g k) :=
  funext (λm, 
  have finite (supp f ∪ supp g), from !finite_union,
  have h1:supp (f+g) ⊆ supp f ∪ supp g, from add_supp_subset_union,
  have finite (supp (f+g)), from add_finite_supp,
  have h2:supp f ⊆ supp f ∪ supp g, by apply subset_union_left,
  have h3:supp g ⊆ supp f ∪ supp g, by apply subset_union_right,
  by rewrite [mul_distrib_aux,↑function.mul,
  (@Sum_exchange _ _ _ _ _ _ _ (supp f) (supp k) _ _),
  (@Sum_exchange _ _ _ _ _ _ _ (supp g) (supp k) _ _),
  -(mul_distrib_right_aux2 _ _ _ _ h2),
  -(mul_distrib_right_aux2 _ _ _ _ h3),-Sum_add,
  (@Sum_exchange _ _ _ _ _ _ _ (supp (f+g)) (supp k) _ _)];
  apply Sum_ext;intros x hx;
  rewrite [-Sum_add,-(mul_distrib_right_aux1 f g (k x)),
  (mul_distrib_right_aux (f+g) (k x) h1)])
  
end distrib

section -- zero_mul
  variables [has_mul A][semiring B](f : A -> B)
  variable [finite (supp f)]

  theorem mul_zero: mul f zero = zero :=
  funext (λa, by rewrite [↑function.mul, zero_empty_supp,
  ↑function.zero,Sum_exchange,Sum_empty])

  theorem zero_mul: mul zero f = zero :=
  funext (λa, by rewrite [↑function.mul,zero_empty_supp,Sum_empty])

end

end function_aux
