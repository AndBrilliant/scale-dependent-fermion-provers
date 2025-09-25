(** Basic definitions for fermion mass hierarchies in Coq *)

Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(** Fermion mass structure *)
Record FermionMass := {
  mass_value : R;
  generation : nat;
  flavor : string;
  mass_pos : (0 < mass_value)%R
}.

(** Scale parameter for running coupling constants *)
Record ScaleParameter := {
  energy : R;
  energy_pos : (0 < energy)%R
}.

(** Basic theorem: fermion masses are positive *)
Theorem fermion_mass_positive : forall m : FermionMass,
  (0 < mass_value m)%R.
Proof.
  intro m.
  exact (mass_pos m).
Qed.

(** Mass hierarchy definition *)
Definition mass_hierarchy (m1 m2 m3 : FermionMass) : Prop :=
  (mass_value m1 < mass_value m2)%R /\ (mass_value m2 < mass_value m3)%R.

(** Example: creating a fermion mass *)
Definition electron_mass : FermionMass.
Proof.
  refine {|
    mass_value := 0.511;
    generation := 1;
    flavor := "electron";
    mass_pos := _
  |}.
  lra.
Defined.