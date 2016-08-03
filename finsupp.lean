import supp sum aux
open set function eq.ops prod.ops classical
-- classical for equiv_def


variables {A B:Type}

section -- add zero neg have finite support

  theorem add_finite_supp [add_monoid B]{f g: A -> B}
  [finite (supp f)][finite (supp g)]: finite (supp (f + g)) :=
    @finite_subset _ _ _ !finite_union add_supp_subset_union

  theorem zero_finite_supp [has_zero B]: finite (supp (@zero A B _)):=
    (@zero_empty_supp A B _)⁻¹ ▸ finite_empty

  theorem neg_finite_supp[add_group B]{f: A -> B}
  [finite (supp f)]: finite (supp (neg f)) :=
    by rewrite neg_supp_eq;assumption

end

section -- one has finite support

  variables [monoid A][semiring B]

  theorem one_finite_supp : finite (supp (@one A B _ _)) :=
    or.elim (@one_supp_empty_or_singleton A B _ _)
    (λh, h⁻¹ ▸ finite_empty)
    (λh, h⁻¹ ▸ (finite_insert 1 ∅))

end

section --mul has finite support
  
  variables [has_mul A][semiring B]
 
  section equiv_def


  noncomputable definition mul₀ (f g: A -> B): A -> B :=
    λa, ∑x∈ supp f * supp g ∩ (λx, a=x.1*x.2), (f x.1)*(g x.2)
  
  lemma mul_equivdef_aux {f g: A -> B}{a:A}: 
  uncurry (λx:A, λy:A, (ite (a=x*y) 1 0)*((f x)*(g y))) =
   (λx:A×A, (ite (a=x.1*x.2) 1 0)*((f x.1)*(g x.2))) := 
  by apply uncurry_curry
  
  corollary mul_equivdef_aux_cor {f g: A -> B}{a:A}: 
  (λx:A, λy:A, (ite (a=x*y) 1 0)*((f x)*(g y))) =
   curry (λx:A×A, (ite (a=x.1*x.2) 1 0)*((f x.1)*(g x.2))) := 
  by apply curry_uncurry


  theorem mul_equivdef (f g:A -> B)[finite (supp f)][finite (supp g)]: 
    mul f g = mul₀ f g :=
    have finite (supp f * supp g), from finite_product,
    funext (λa, by rewrite [↑function.mul,↑mul₀,-Sum_uncurry,
      mul_equivdef_aux,Sum_reduced])
  
  end equiv_def

  section finite_supp 
  
  abbreviation img (f g: A-> B):= image (uncurry mul) (supp f * supp g)
  local abbreviation domain (f g: A->B)(a:A):= 
    supp f * supp g ∩ (λx, a=x.1*x.2)

  lemma zero_of_empty_domain{f g:A->B}{a:A} (h: domain f g a = ∅): 
    mul₀ f g a = 0 :=
    by rewrite [↑mul₀,h,Sum_empty]
  
  lemma ne_empty_domain_ne_zero{f g:A-> B}{a:A}(h: mul₀ f g a ≠ 0): 
    domain f g a ≠∅ :=
    assume hemp: domain f g a = ∅, absurd (zero_of_empty_domain hemp) h
  
  lemma mul₀_supp_subset_img (f g:A-> B) : supp (mul₀ f g) ⊆ img f g := 
    λ x h, have mul₀ f g x ≠ 0, from h, 
    obtain (t:A×A)(ht: t ∈ domain f g x), 
    from exists_mem_of_ne_empty (ne_empty_domain_ne_zero this),
    have hin: t∈supp f * supp g, from and.left ht,
    have t∈(λa,x=a.1*a.2),from and.right ht,
    have hx:x = (uncurry mul) t, from proof
      have ha:x=t.1*t.2, from this,
      have hb:t.1*t.2 = uncurry mul t, from match t with (a,b):= rfl end,
      by rewrite [ha,hb] qed,
    have (uncurry mul) t∈img f g, 
    from mem_image_of_mem (uncurry mul) hin,
    show x∈ img f g, by rewrite hx;exact this 
  

  theorem finite_img(f g: A->B)[finite (supp f)][finite (supp g)]: 
    finite (img f g):=
    @finite_image _ _ _ _ finite_product

  theorem mul_supp_subset_img (f g:A-> B)[finite (supp f)][finite (supp g)] : 
    supp (mul f g) ⊆ img f g := 
     by rewrite [(mul_equivdef f g)];apply mul₀_supp_subset_img  

  theorem mul_finite_supp {f g: A-> B}[finite (supp f)][finite (supp g)]:
    finite (supp (mul f g)) :=
    have finite (supp (mul₀ f g)), 
    from @finite_subset _ _ _ (finite_img f g) (mul₀_supp_subset_img f g),
    by rewrite (mul_equivdef f g);exact this

  end finite_supp

end
