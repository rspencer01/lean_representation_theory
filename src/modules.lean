import algebra.module
import ring_theory.algebra
import algebra.punit_instances

variables (R : Type) [ring R]

class modules :=
  (space : Type)
  [acg : add_comm_group space]
  [mod : module R space]

variable (M : modules R)

instance modules_add_comm_group : add_comm_group M.space := modules.acg R
instance modules_module : module R M.space := modules.mod R
instance modules_of_module (M : Type) [add_comm_group M] [module R M] : modules R := {space:=M, acg:= infer_instance, mod:=infer_instance}

instance modules_to_type : has_coe (modules R) Type := ⟨ λ R, R.space ⟩ 
instance modules_type_acg : add_comm_group (M : Type) := modules_add_comm_group R M
instance modules_type_module : module R (M : Type) := modules_module R M

-- An example of a module for any ring is the zero module
instance zero_module : module R punit := module.of_core $ 
  by refine {
    smul := λ _ _, punit.star,
    .. punit.comm_ring, ..}; 
    intros; exact subsingleton.elim _ _

@[simp]
def submodules {R} [ring R] (M : modules R) := submodule R (M : Type)

@[simp]
instance {R} [ring R] (M : modules R) : has_zero (submodules M) :=
  ⟨{
    carrier := {(0 : (M : Type))},
    zero := by simp,
    add := sorry,
    smul := sorry
  }⟩

instance {R} [ring R] (M : modules R) : inhabited (submodules M) := ⟨(0 : submodules M)⟩
instance {R} [ring R] (M : Type) [add_comm_group M] [module R M] : inhabited (submodule R M) := sorry

instance : has_coe (submodules M) (modules R) :=
  ⟨λ N,
  {
    space := N.carrier,
    acg := N.add_comm_group,
    mod := N.module,
  }⟩

namespace submodules
  def lift' (N : submodules M) (V : submodules (N : modules R)) : submodules M := {
    carrier := N.carrier,
    zero := N.zero,
    add := N.add,
    smul := N.smul
  }
end submodules

instance : lattice.complete_lattice (submodules M) := (by dunfold submodules; apply_instance)

variable (N : submodules M)

def mods_quotient : modules R := {
  space := submodule.quotient N,
  acg := by apply_instance,
  mod := by apply_instance
}

#check mods_quotient