import algebra.group_bigops data.nat data.finset data.set
import aux
 
structure add_left_cancel_monoid [class] (A:Type) extends add_monoid A, add_left_cancel_semigroup A

structure add_right_cancel_monoid [class] (A:Type) extends add_monoid A, add_right_cancel_semigroup A

structure add_comm_cancel_monoid [class] (A:Type) extends add_comm_monoid A, add_left_cancel_semigroup A

  definition add_comm_cancel_monoid.to_add_left_cancel_monoid [trans_instance]{A:Type}[add_comm_cancel_monoid A] :
    add_left_cancel_monoid A :=
    {| add_left_cancel_monoid, 
       add := add,
       zero := zero,
       add_assoc := add_comm_cancel_monoid.add_assoc,
       add_zero := add_zero,
       zero_add := zero_add,
       add_left_cancel := add_comm_cancel_monoid.add_left_cancel |}

structure comm_cancel_monoid [class] (A:Type) extends comm_monoid A, left_cancel_semigroup A

namespace comm_cancel_monoid
  open eq.ops set classical prod.ops
  variables {A:Type}[comm_cancel_monoid A]
 
  theorem mul_right_cancel (a b c :A)(h: b * a = c * a) : b = c :=
    have a * b = a * c, from (mul_comm a b) ⬝ (h ⬝ (mul_comm c a)),
    mul_left_cancel a b c this


  theorem equiv_pred (a b: A):(λx,a= x*b) = (λx,a=b*x) :=
   ext (λx, iff.intro 
   (λ l, have a = x*b, from l,
     have a = b*x, from eq.trans this (mul_comm x b),
     show x∈(λx,a=b*x), from this)
   (λ r, have a = b*x, from r,
     have a = x*b, from eq.trans this (mul_comm b x),
     show x∈(λx,a=x*b), from this))


  theorem empty_or_singleton_right (m n:A):
    (λx,m=n*x) = ∅ ∨ ∃ u:A, (λx,m=n*x) = '{u}:=
    or.elim (em ((λx,m=n*x) = ∅))
    (assume emp, or.inl emp)
    (assume nemp, obtain (u:A)(hu:u∈λx,m=n*x),
    from exists_mem_of_ne_empty nemp,
    have (λx,m=n*x)='{u},from proof
      singleton_of_all_eq_of_ne_empty (λ (y:A) (hy:y∈λx,m=n*x), 
      mul_left_cancel n y u (hy ▸ hu)) nemp qed,
    or.inr (exists.intro u this))

   theorem empty_or_singleton_left (m n: A):
    (λx,m=x*n) = ∅ ∨ ∃ u:A, (λx,m=x*n) = '{u}:=
    by rewrite (equiv_pred m n);
    apply empty_or_singleton_right
    
end comm_cancel_monoid

namespace nat

definition to_add_left_cancel_monoid [instance]: add_left_cancel_monoid ℕ :=
{|add_left_cancel_monoid,
  add := nat.add,
  zero := nat.zero,
  add_assoc := nat.add_assoc,
  zero_add := nat.zero_add,
  add_zero := nat.add_zero,
  add_left_cancel := @nat.add_left_cancel|}

definition to_add_right_cancel_monoid [instance]: add_right_cancel_monoid ℕ :=
{|add_right_cancel_monoid,
  add := nat.add,
  zero := nat.zero,
  add_assoc := nat.add_assoc,
  zero_add := nat.zero_add,
  add_zero := nat.add_zero,
  add_right_cancel := @nat.add_right_cancel|}

definition to_add_comm_cancel_monoid [instance]: add_comm_cancel_monoid ℕ :=
{| add_comm_cancel_monoid,
   add := nat.add,
   zero := nat.zero,
   add_assoc := nat.add_assoc,
   zero_add := nat.zero_add,
   add_zero := nat.add_zero,
   add_left_cancel := @nat.add_left_cancel,
   add_comm := nat.add_comm
|}

-- for any comm and left cancel monoid, right cancel also holds

end nat

namespace finset -- define mul_Sum on semiring

  variables {A B:Type}[decidable_eq A][semiring B]
  proposition semiring.mul_Sum (f : A → B) {s : finset A} (b : B) :
    b * (∑ x ∈ s, f x) = ∑ x ∈ s, b * f x :=
  begin
    induction s with a s ans ih,
    {rewrite [+Sum_empty, mul_zero]},
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem (λ x, b * f x) ans],
    rewrite [-ih, left_distrib]
  end

  proposition semiring.Sum_mul (f : A → B) {s : finset A} (b : B) :
    (∑ x ∈ s, f x) * b = ∑ x ∈ s, f x * b :=
   begin
    induction s with a s ans ih,
    {rewrite [+Sum_empty, zero_mul]},
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem (λ x, f x * b) ans],
    rewrite [-ih, right_distrib]
  end
  
end finset


namespace set
  open classical
  variables {A B:Type}[decidable_eq A][semiring B]
  proposition semiring.mul_Sum (f : A → B) {s : set A} (b : B) :
    b * (∑ x ∈ s, f x) = ∑ x ∈ s, b * f x :=
  begin
    cases (em (finite s)) with fins nfins,
    rotate 1,
      {rewrite [+Sum_of_not_finite nfins, mul_zero]},
    induction fins with a s fins ans ih,
      {rewrite [+Sum_empty, mul_zero]},
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem (λ x, b * f x) ans],
    rewrite [-ih, left_distrib]
  end

  proposition semiring.Sum_mul (f : A → B) {s : set A} (b : B) :
    (∑ x ∈ s, f x) * b = ∑ x ∈ s, f x * b :=
   begin
    cases (em (finite s)) with fins nfins,
    rotate 1,
      {rewrite [+Sum_of_not_finite nfins, zero_mul]},
    induction fins with a s fins ans ih,
      {rewrite [+Sum_empty, zero_mul]},
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem (λ x,f x * b) ans],
    rewrite [-ih, right_distrib]
  end


end set
