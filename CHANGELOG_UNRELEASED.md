# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal.v`:
  + lemmas `esum_ninfty`, `esum_pinfty`
  + lemmas `addeoo`, `daddeoo`
  + lemmas `desum_pinfty`, `desum_ninfty`
- in `Rstruct.v`:
  + lemmas `Rsupremums_neq0`, `Rsup_isLub`, `Rsup_ub`
- in `classical_sets.v`:
  + lemma `supremum_out`
  + definition `isLub`
  + lemma `supremum1`
- in `reals.v`:
  + lemma `emptyN`, `ubound0`, `lboundT`

### Changed

- in `trigo.v`:
  + the `realType` argument of `pi` is implicit
  + the printed type of `acos`, `asin`, `atan` is `R -> R`
- in `Rstruct.v`:
  + statement of lemma `completeness'`, renamed to `Rcondcomplete`
  + statement of lemma `real_sup_adherent`
- in `ereal.v`:
  + statements of lemmas `ub_ereal_sup_adherent`, `lb_ereal_inf_adherent`
- in `reals.v`:
  + definition `sup`
  + statements of lemmas `sup_adherent`, `inf_adherent`

### Renamed

- in `ereal.v`:
  + `esum_pinfty` -> `esum_ord_pinfty`
  + `esum_ninfty` -> `esum_ord_ninfty`
  + `desum_pinfty` -> `desum_ord_pinfty`
  + `desum_ninfty` -> `desum_ord_ninfty`
- `has_sup1`, `has_inf1` moved from `reals.v` to `classical_sets.v`
- in `reals.v`:
  + type generalization of `has_supPn`
- in `classical_sets.v`:
  + `supremums_set1` -> `supremums1`
  + `infimums_set1` -> `infimums1`

### Removed

- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`
  + lemmas `desum_fset_pinfty`, `desum_fset_ninfty`
- in `Rstruct.v`:
  + definition `real_sup`
  + lemma `real_sup_is_lub`, `real_sup_ub`, `real_sup_out`
- in `reals.v`:
  + field `sup` from `mixin_of` in module `Real`

### Infrastructure

### Misc
