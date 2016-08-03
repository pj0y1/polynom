/- Define supp and zero-/
import algebra.group_bigops data.set
open classical set

namespace function

  /- supp and zero-/
  section 
  variables {A B: Type}[has_zero B]

  definition supp (f: A -> B): A -> Prop := 
    λa, f a ≠ (0:B)

  theorem ne_zero_iff_mem_supp{f: A -> B}{a: A}:
    (f a ≠ 0) ↔ a∈ supp f :=
    iff.intro (λl, l)(λr, r)

  corollary ne_zero_eq_mem_supp(f: A -> B)(a: A):
    (f a ≠ 0) = (a∈ supp f) :=
    propext ne_zero_iff_mem_supp

  theorem eq_zero_iff_not_mem_supp{f: A -> B}{a: A}: 
    (f a = 0) ↔ a∉ supp f :=
    iff.intro 
      (λl, or.elim (em (a∈supp f)) 
        (λh, absurd l (iff.mpr ne_zero_iff_mem_supp h))
        (λh, h))
      (λr, or.elim (em (f a = 0))
        (λh, h)
        (λh, absurd (iff.mp ne_zero_iff_mem_supp h) r))

  corollary eq_zero_eq_not_mem_supp(f: A -> B)(a: A): 
    (f a = 0) = ( a∉ supp f) :=
    propext eq_zero_iff_not_mem_supp


  definition zero : A -> B := λa, (0:B)

  theorem zero_empty_supp : supp (@zero A B _)= ∅ :=
    eq_empty_of_forall_not_mem 
    (λ x, iff.mp eq_zero_iff_not_mem_supp (show (λa:A, 0) x = 0, from rfl))

  end

  definition add {A B:Type}[has_add B](f g:A -> B): A -> B :=
    λa, add (f a) (g a)
  
  notation f + g := add f g
  
  theorem add_assoc {A B:Type}[add_semigroup B](f g h: A -> B):
    (f + g) + h = f + (g + h) :=
    funext (λa, !add_semigroup.add_assoc)
 
  theorem add_comm {A B:Type}[add_comm_semigroup B](f g: A -> B):
    f + g = g + f :=
    funext (λa, !add_comm_semigroup.add_comm)

  theorem add_zero {A B:Type}[add_monoid B](f: A -> B):
    f + zero = f :=
    funext (λa, !add_monoid.add_zero)

  theorem zero_add {A B:Type}[add_monoid B](f: A -> B):
    zero + f = f :=
    funext (λa, !add_monoid.zero_add)

  theorem add_left_cancel {A B:Type}[add_left_cancel_semigroup B](f g h: A -> B)
   (H: f + g = f + h): g = h := 
     have ∀a:A, f a + g a = f a + h a, from λa, 
     by rewrite [↑add at H]; apply congr H (eq.refl a),
     funext (λa, !add_left_cancel_semigroup.add_left_cancel (this a))

  theorem add_right_cancel {A B:Type}[add_right_cancel_semigroup B](f g h: A -> B)
   (H: g + f = h + f): g = h :=
     funext (λa, by rewrite [↑add at H];
     apply !add_right_cancel_semigroup.add_right_cancel; 
     apply congr H (eq.refl a))

  theorem add_supp_subset_union {A B:Type}[add_monoid B]{f g: A -> B}:
    supp (f + g) ⊆ supp f ∪ supp g :=
    λ x H, by_contradiction
    assume Hn: x ∉ (supp f) ∪ (supp g), 
    have x ∈ -(supp f ∪ supp g), from mem_compl Hn,
    have x ∈ (-supp f) ∩ (-supp g), from eq.subst !compl_union this,
    have Hf : f x = 0, by rewrite (eq_zero_eq_not_mem_supp f x);
    apply (not_mem_of_mem_compl (and.left this)),
    have Hg : g x = 0, by rewrite (eq_zero_eq_not_mem_supp g x);
    apply (not_mem_of_mem_compl (and.right this)),
    have Heq: f x + g x = 0, by rewrite [Hf, Hg];simp,
    have (f + g) x = 0, from Heq,
    have x∉supp (f + g), 
    by rewrite [(eq_zero_eq_not_mem_supp (f + g) x) at this];exact this,
    show false, from absurd H this


  definition neg {A B:Type}[has_neg B](f: A -> B): A -> B :=
    λa, neg (f a)

  theorem neg_zero {A B:Type}[add_group B]: neg (@zero A B _) = zero :=
    funext (λa, !neg_zero)

  theorem add_left_inv {A B:Type}[add_group B]{f:A -> B}:
    (neg f) + f = zero :=
    funext (λa, !add_group.add_left_inv)
  
  theorem neg_supp_eq {A B:Type}[add_group B]{f: A -> B}: supp (neg f) = supp f :=
    ext (λ x, iff.intro 
    (assume l, have neg f x ≠ 0, from l, 
      have f x ≠ 0, from assume h: f x = 0, 
      absurd (iff.mpr !neg_eq_zero_iff_eq_zero h) this,
      show x ∈ supp f, 
      by rewrite [(ne_zero_eq_mem_supp f x) at this];exact this) 
    (assume r, have f x ≠ 0, from r,
      have neg f x ≠ 0, from assume h: neg f x = 0, 
      absurd (eq_zero_of_neg_eq_zero h) this,
      show x ∈ supp (neg f), 
      by rewrite [(ne_zero_eq_mem_supp (neg f) x) at this];exact this))

  section --defining One

  variables {A B:Type}[monoid A][semiring B]
  
  noncomputable definition one: A -> B := λa, ite (a=(1:A)) 1 0

  /- one supp-/
  lemma one_supp_singleton (H:(0:B)≠(1:B)): supp (@one A B _ _) = '{1} :=
   ext (λx:A, iff.intro
   (λl, have hne:(@one A B _ _) x ≠ (0:B), 
    from (iff.mpr ne_zero_iff_mem_supp) l,
    have h1: x=(1:A), from proof
    by_contradiction assume h:¬ x =(1:A), 
    have x≠(1:A), from h,
    have (one x) = (0:B), from if_neg this,
    absurd this hne qed,
    mem_singleton_of_eq h1)
   (λr, have x=(1:A), from eq_of_mem_singleton r,
    have h2:(one x) =(1:B), from if_pos this,
    have (0:B) ≠ (one x), by rewrite h2; apply H,
    have (one x) ≠ (0:B), by inst_simp,
    by rewrite ne_zero_eq_mem_supp at this;exact this))
  
  lemma one_supp_empty (H:(0:B)=(1:B)): supp(@one A B _ _) =∅ :=
    have hx:∀x:A, one x = (0:B), from proof
    λx:A, or.elim (em (x = 1))
    (λh, eq.subst (eq.symm H) (if_pos h))
    (λh, if_neg h) qed,
    by apply eq_empty_of_forall_not_mem;intro x;
    rewrite [-(@eq_zero_eq_not_mem_supp A B _ one x)];exact (hx x)

  theorem one_supp_empty_or_singleton : 
    supp (@one A B _ _) = ∅ ∨ supp (@one A B _ _) = '{1} :=
    or.elim (em ((0:B)=(1:B)))
    (λheq, or.inl (one_supp_empty heq))
    (λhne, or.inr (one_supp_singleton hne))

  end


  section --Mul 
  
  variables {A B:Type}[has_mul A][semiring B]
  
  noncomputable definition mul (f g: A -> B): A -> B := 
  λa, ∑x∈ supp f,∑y∈ supp g, (ite (a=x*y) 1 0)*((f x)*(g y))
  -- a simple by trick by add brackets ((f x)*(g y))

  end 

end function


