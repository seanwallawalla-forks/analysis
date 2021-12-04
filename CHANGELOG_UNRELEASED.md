# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + definitions `kolmogorov_space`, `accessible_space`
  + lemmas `accessible_closed_set1`, `accessible_kolmogorov`
- in `ereal.v`:
  + lemmas `lee_pemull`, `lee_nemul`, `lee_pemulr`, `lee_nemulr`
- in `sequences.v`:
  + lemmas `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`,
    `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`
- in `ereal.v`:
  + lemma `fin_numM`
  + definition `mule_def`, notation `x *? y`
  + lemma `mule_defC`
  + notations `\*` in `ereal_scope`, and `ereal_dual_scope`

### Changed

- in `topology.v`:
  + renamed and generalized `setC_subset_set1C` implication to
    equivalence `subsetC1`
- in `ereal.v`:
  + lemmas `ereal_sup_gt`, `ereal_inf_lt` now use `exists2`
- notation `\*` moved from `realseq.v` to `topology.v`
- in `posnum.v`:
  + lemmas `pos_le_maxl`, `pos_le_minr`
- in `ereal.v`:
  + lemmas `lee_paddl`, `lte_addl`, `lee_paddr`, `lte_paddr`, `lee_lt_add`
- in `ereal.v`:
  + definitions `ereal_dnbhs` and `ereal_nbhs` changed to use large inequality instead
    of strict inequality
- in `normedtype.v`:
  + definitions `pinfty_dnbhs` and `ninfty_nbhs` changed to use large inequality instead
    of strict inequality

### Renamed

- in `topology.v:
  + `hausdorff` -> `hausdorff_space`

### Removed

- in `realseq.v`:
  + notation `\-`

### Infrastructure

### Misc
