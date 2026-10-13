# Per-file compilation times (`lean/Meijer5255`)

Measured 2026-10-13, sequentially, one `lake env lean Meijer5255/<File>.lean` per file (all
dependencies already built), Windows 11, 8 threads / 32 GB. Every file: exit code 0, 0 errors;
the only `sorry` is `PNT.prime_number_theorem`. About 23.5 s of each time is loading the
`import Mathlib` environment (cf. `PNT`, 20 lines, 23.6 s); files that import only a few Mathlib
modules (`QGrowth_GW_fast`, `_cert*`, `_poly`) load faster.

**Total: 1742 s (29.0 min) for 70 files, 24328 lines.**

| file | time (s) | lines |
|---|---:|---:|
| `BaselineIntegrality` | 27.6 | 437 |
| `BaselineIntegrality_Aux` | 28.4 | 397 |
| `BaselineProfile` | 27.0 | 326 |
| `BaselineProfile_Cells` | 30.8 | 292 |
| `BaselineProfile_Jets` | 25.9 | 344 |
| `BaselineProfile_Perm` | 25.3 | 413 |
| `BaselineProfile_Upper` | 26.0 | 429 |
| `Blueprint_5255` | 29.7 | 541 |
| `CarryFacts` | 26.4 | 230 |
| `CarryFacts_Cells` | 26.1 | 160 |
| `CmfReadout` | 31.0 | 497 |
| `CmfReadout_Aux` | 26.2 | 235 |
| `CmfReadout_PF` | 26.2 | 696 |
| `CmfReadout_Path` | 33.2 | 398 |
| `GnewDvd` | 24.5 | 198 |
| `LinformError` | 33.6 | 307 |
| `LogGnewGe` | 30.0 | 760 |
| `LogGnewGe_Aux` | 24.7 | 279 |
| `LogGnewGe_Cert` | 28.7 | 95 |
| `LogNormalizationLe` | 24.7 | 202 |
| `PNT` | 23.6 | 20 |
| `QGrowth` | 26.6 | 234 |
| `QGrowth_Bridge` | 24.7 | 175 |
| `QGrowth_CMF_basic` | 25.0 | 420 |
| `QGrowth_CMF_det` | 26.5 | 538 |
| `QGrowth_CMF_kernel` | 27.4 | 478 |
| `QGrowth_CMF_main` | 24.6 | 374 |
| `QGrowth_CMF_pairing` | 27.4 | 349 |
| `QGrowth_CMF_path` | 29.0 | 708 |
| `QGrowth_CMF_transport` | 25.1 | 380 |
| `QGrowth_GW_Sbound` | 25.4 | 246 |
| `QGrowth_GW_bridge` | 24.7 | 348 |
| `QGrowth_GW_cert0` | 7.5 | 14 |
| `QGrowth_GW_cert1` | 7.5 | 14 |
| `QGrowth_GW_cert2` | 7.5 | 14 |
| `QGrowth_GW_cert3` | 7.5 | 14 |
| `QGrowth_GW_cert4` | 7.5 | 14 |
| `QGrowth_GW_cert5` | 7.5 | 14 |
| `QGrowth_GW_cone` | 26.5 | 447 |
| `QGrowth_GW_fast` | 4.2 | 373 |
| `QGrowth_GW_limit` | 24.1 | 164 |
| `QGrowth_GW_poly` | 11.3 | 297 |
| `QGrowth_Mfun_sub_Mfun_pred` | 25.2 | 457 |
| `QGrowth_PF` | 25.7 | 560 |
| `QGrowth_Star` | 40.4 | 235 |
| `QGrowth_ZetasAux` | 29.5 | 654 |
| `QGrowth_coeffMat_zero` | 25.1 | 200 |
| `QGrowth_cross_product_readout` | 26.6 | 1003 |
| `QGrowth_defs` | 24.1 | 280 |
| `QGrowth_derivSum_eq_realize_Lfun` | 24.3 | 200 |
| `QGrowth_det_V_eq` | 24.1 | 124 |
| `QGrowth_growth_estimates` | 28.2 | 717 |
| `QGrowth_pairing_identity` | 29.4 | 318 |
| `SecondOrderShell` | 23.6 | 26 |
| `ShellFirstOrder` | 24.5 | 417 |
| `ShellFirstOrder_Cert` | 44.1 | 434 |
| `ShellFirstOrder_Core` | 26.9 | 845 |
| `ShellFirstOrder_Gen` | 25.0 | 573 |
| `TraceLemma` | 25.8 | 975 |
| `TraceLemma_Cls` | 24.3 | 205 |
| `TraceLemma_Loc` | 24.7 | 473 |
| `TraceLemma_Res` | 25.1 | 167 |
| `TraceLemma_Val` | 24.2 | 308 |
| `WindowReadout` | 25.5 | 532 |
| `WindowReadout_Bounds` | 24.8 | 253 |
| `WindowReadout_Residue` | 24.5 | 350 |
| `WindowRootData` | 31.9 | 483 |
| `WindowRootData_Aux` | 24.3 | 79 |
| `WindowRootData_Cert` | 28.8 | 306 |
| `definitions` | 33.9 | 283 |

## By node (node file + its helpers)

| group | files | time (s) | lines |
|---|---:|---:|---:|
| BaselineIntegrality | 2 | 56.0 | 834 |
| BaselineProfile | 5 | 135.0 | 1804 |
| Blueprint | 1 | 29.7 | 541 |
| CarryFacts | 2 | 52.5 | 390 |
| CmfReadout | 4 | 116.6 | 1826 |
| GnewDvd | 1 | 24.5 | 198 |
| LinformError | 1 | 33.6 | 307 |
| LogGnewGe | 3 | 83.4 | 1134 |
| LogNormalizationLe | 1 | 24.7 | 202 |
| PNT | 1 | 23.6 | 20 |
| QGrowth | 1 | 26.6 | 234 |
| QGrowth_* (analytic layer) | 31 | 673.5 | 10129 |
| SecondOrderShell | 1 | 23.6 | 26 |
| ShellFirstOrder | 4 | 120.5 | 2269 |
| TraceLemma | 5 | 124.1 | 2128 |
| WindowReadout | 3 | 74.8 | 1135 |
| WindowRootData | 3 | 85.0 | 868 |
| definitions | 1 | 33.9 | 283 |
