/- ℕ is a add_comm_cancel_monoid 
(Π A B:Type , A -> B) shares the same algebra structure with B,
thus monomial:A -> ℕ is add_comm_cancel_monoid, hence proved
comm_cancel_monoid A -> semiring B, is euqivalent as proving
polynomial property
-/

import mul_aux
open classical -- for ite
open set function subtype
open function_aux

set_option unifier.max_steps 180000

definition proto (A B:Type)[has_zero B]: Type := 
  subtype (λf: A-> B, finite (supp f))

namespace proto -- prototype for both monomials and polynomials

  variables {A B:Type}

  definition add [add_monoid B](f g: proto A B): proto A B :=
    tag (elt_of f + elt_of g) 
    (@add_finite_supp _ _ _ _ _ (has_property f)(has_property g))
  
--  notation f `**` g := add f g
  
  theorem add_comm [add_comm_monoid B](f g:proto A B): add f g = add g f :=
  by apply subtype.eq; apply function.add_comm

  theorem add_assoc [add_monoid B](f g h:proto A B): add (add f g) h = add f (add g h):=
  by apply subtype.eq; apply function.add_assoc

  definition zero [add_monoid B]: proto A B :=
    tag (function.zero)
    (by rewrite zero_empty_supp;apply finite_empty)

  theorem zero_add [add_monoid B](f: proto A B): add zero f = f :=
    by apply subtype.eq; apply function.zero_add

  theorem add_zero [add_monoid B](f: proto A B): add f zero = f :=
    by apply subtype.eq; apply function.add_zero

  definition to_comm_monoid[instance][add_comm_monoid B]: comm_monoid (proto A B):=
    {| comm_monoid, 
       mul := add,
       mul_comm := add_comm,
       mul_assoc := add_assoc,
       one := zero,
       one_mul := zero_add,
       mul_one := add_zero
    |}

  definition to_monoid[instance][add_monoid B]: monoid (proto A B):=
    {| monoid, 
       mul := add,
       mul_assoc := add_assoc,
       one := zero,
       one_mul := zero_add,
       mul_one := add_zero
    |}
  
  theorem add_left_cancel [add_left_cancel_monoid B] (f g h: proto A B)
  (H: add f g = add f h): g = h :=
    have elt_of f + elt_of g = elt_of f + elt_of h, from congr (eq.refl elt_of) H,
    by apply subtype.eq; apply function.add_left_cancel (elt_of f);exact this

  theorem add_right_cancel [add_right_cancel_monoid B]{f g h: proto A B}
  (H: add g f= add h f): g = h :=
    have elt_of g + elt_of f = elt_of h + elt_of f, from congr (eq.refl elt_of) H,
    by apply subtype.eq; apply function.add_right_cancel (elt_of f);exact this

  /-This is exactly ℕ (without considering order)-/
  definition to_comm_cancel_monoid [instance][add_comm_cancel_monoid B]: comm_cancel_monoid (proto A B):=
  {| comm_cancel_monoid,
     mul := add,
     one := zero,
     mul_assoc := add_assoc,
     mul_comm := add_comm,
     mul_one := add_zero,
     one_mul := zero_add,
     mul_left_cancel := add_left_cancel |}


  definition inv [add_group B](f: proto A B): proto A B := 
    tag (neg (elt_of f)) (@neg_finite_supp _ _ _ _ (has_property f))

  theorem add_left_inv [add_group B](f: proto A B): add (inv f) f = zero :=
    by apply subtype.eq; apply function.add_left_inv

  definition to_group [instance][add_group B]: group (proto A B) :=
  {| group,
     mul := add,
     one := zero,
     mul_assoc := add_assoc,
     one_mul := zero_add,
     mul_one := add_zero,
     mul_left_inv := add_left_inv|}

  definition to_comm_group [instance][add_comm_group B]: comm_group (proto A B):=
  {|comm_group,
    mul := add,
    one := zero,
    mul_assoc := add_assoc,
    mul_comm := add_comm,
    one_mul := zero_add,
    mul_one := add_zero,
    mul_left_inv := add_left_inv|}

  section

    variable [semiring B]
    
    noncomputable definition mul[has_mul A](f g: proto A B): 
      proto A B :=
    tag (function.mul (elt_of f) (elt_of g))
    (@mul_finite_supp _ _ _ _ _ _ (has_property f) (has_property g))


    theorem mul_assoc [comm_cancel_monoid A](f g k:proto A B):
      mul (mul f g) k =  mul f (mul g k) :=
    have finite (supp (elt_of f)), from has_property f,
    have finite (supp (elt_of g)), from has_property g,
    have finite (supp (elt_of k)), from has_property k,
    by apply subtype.eq; apply function_aux.mul_assoc

    noncomputable definition one [monoid A]: proto A B :=
    tag (@function.one A B _ _)(one_finite_supp)

    theorem mul_one [monoid A](f:proto A B):
      mul f one = f :=
    have finite (supp (elt_of f)), from has_property f,
    by apply subtype.eq; apply function_aux.mul_one

    theorem one_mul [monoid A](f:proto A B):
      mul one f  = f :=
    have finite (supp (elt_of f)), from has_property f,
    by apply subtype.eq ; apply function_aux.one_mul

   
    theorem mul_zero [has_mul A](f:proto A B):
      mul f proto.zero = proto.zero :=
    have finite (supp (elt_of f)), from has_property f,
    by apply subtype.eq; apply function_aux.mul_zero


    theorem zero_mul [monoid A](f:proto A B):
      mul zero f  = zero :=
    have finite (supp (elt_of f)), from has_property f,
    by apply subtype.eq; apply function_aux.zero_mul
    

    theorem mul_left_distrib [has_mul A](f g k:proto A B):
    mul f (add g k) = add (mul f g) (mul f k) :=
    have finite (supp (elt_of f)), from has_property f,
    have finite (supp (elt_of g)), from has_property g,
    have finite (supp (elt_of k)), from has_property k,
    by apply subtype.eq; apply function_aux.mul_left_distrib

    theorem mul_right_distrib [has_mul A](f g k:proto A B):
    mul (add f g) k = add (mul f k) (mul g k) :=
    have finite (supp (elt_of f)), from has_property f,
    have finite (supp (elt_of g)), from has_property g,
    have finite (supp (elt_of k)), from has_property k,
    by apply subtype.eq; apply function_aux.mul_right_distrib


    noncomputable definition to_semiring [instance][comm_cancel_monoid A]:
     semiring (proto A B):=
    {| semiring,
       add := add,
       add_comm := add_comm,
       add_assoc := add_assoc,
       zero := zero,
       add_zero := add_zero,
       zero_add := zero_add,
       mul := mul,
       mul_assoc := mul_assoc,
       mul_zero := mul_zero,
       zero_mul := zero_mul,
       one := one,
       mul_one := mul_one,
       one_mul := one_mul,    
       left_distrib := mul_left_distrib,
       right_distrib := mul_right_distrib |}

  end
  
  section

    variable [comm_semiring B]

    theorem mul_comm[comm_semigroup A](f g : proto A B):
      mul f g = mul g f :=  
    have finite (supp (elt_of f)), from has_property f,
    have finite (supp (elt_of g)), from has_property g,
    by apply subtype.eq; apply function_aux.mul_comm

  
    noncomputable definition to_comm_semiring [instance][comm_cancel_monoid A]:
     comm_semiring (proto A B):=
    {| comm_semiring,
       add := add,
       add_comm := add_comm,
       add_assoc := add_assoc,
       zero := zero,
       add_zero := add_zero,
       zero_add := zero_add,
       mul := mul,
       mul_assoc := mul_assoc,
       mul_zero := mul_zero,
       zero_mul := zero_mul,
       one := one,
       mul_one := mul_one,
       one_mul := one_mul,    
       left_distrib := mul_left_distrib,
       right_distrib := mul_right_distrib,
       mul_comm := mul_comm|}

  end

  section

    variable [ring B]
    noncomputable definition to_ring [instance][comm_cancel_monoid A]:
      ring (proto A B) :=
    {| ring,
       add := add,
       add_comm := add_comm,
       add_assoc := add_assoc,
       zero := zero,
       add_zero := add_zero,
       zero_add := zero_add,
       neg := inv,
       add_left_inv := add_left_inv,
       mul := mul,
       mul_assoc := mul_assoc,
       one := one,
       mul_one := mul_one,
       one_mul := one_mul,    
       left_distrib := mul_left_distrib,
       right_distrib := mul_right_distrib |}
    
  end

  section

    variable [comm_ring B]
    noncomputable definition to_comm_ring [instance][comm_cancel_monoid A]:
      comm_ring (proto A B) :=
    {| comm_ring,
       add := add,
       add_comm := add_comm,
       add_assoc := add_assoc,
       zero := zero,
       add_zero := add_zero,
       zero_add := zero_add,
       neg := inv,
       add_left_inv := add_left_inv,
       mul := mul,
       mul_comm := mul_comm,
       mul_assoc := mul_assoc,
       one := one,
       mul_one := mul_one,
       one_mul := one_mul,    
       left_distrib := mul_left_distrib,
       right_distrib := mul_right_distrib |}
    
  end

end proto

