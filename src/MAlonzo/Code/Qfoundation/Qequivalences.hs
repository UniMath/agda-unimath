{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qequivalences where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Zsystems
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QpathZ45ZsplitZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QsubtypeZ45ZidentityZ45Zprinciple
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qsubtypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs
import qualified MAlonzo.Code.Qfoundation.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qsubtypes

-- foundation.equivalences._.emb-equiv
d_emb'45'equiv_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'equiv_16 ~v0 ~v1 ~v2 ~v3 v4 = du_emb'45'equiv_16 v4
du_emb'45'equiv_16 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_emb'45'equiv_16 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
         (coe v0))
      (\ v1 v2 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'emb'45'is'45'equiv_878)
-- foundation.equivalences._.eq-transpose-equiv
d_eq'45'transpose'45'equiv_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_eq'45'transpose'45'equiv_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_eq'45'transpose'45'equiv_40
du_eq'45'transpose'45'equiv_40 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_eq'45'transpose'45'equiv_40
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_equiv'45'ap_912))
      (coe
         MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_equiv'45'concat''_166)
-- foundation.equivalences._.map-eq-transpose-equiv
d_map'45'eq'45'transpose'45'equiv_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_map'45'eq'45'transpose'45'equiv_50 = erased
-- foundation.equivalences._.inv-map-eq-transpose-equiv
d_inv'45'map'45'eq'45'transpose'45'equiv_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_inv'45'map'45'eq'45'transpose'45'equiv_60 = erased
-- foundation.equivalences._.triangle-eq-transpose-equiv
d_triangle'45'eq'45'transpose'45'equiv_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'eq'45'transpose'45'equiv_72 = erased
-- foundation.equivalences._.map-eq-transpose-equiv'
d_map'45'eq'45'transpose'45'equiv''_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_map'45'eq'45'transpose'45'equiv''_84 = erased
-- foundation.equivalences._.inv-map-eq-transpose-equiv'
d_inv'45'map'45'eq'45'transpose'45'equiv''_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_inv'45'map'45'eq'45'transpose'45'equiv''_92 = erased
-- foundation.equivalences._.triangle-eq-transpose-equiv'
d_triangle'45'eq'45'transpose'45'equiv''_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'eq'45'transpose'45'equiv''_102 = erased
-- foundation.equivalences.tr-precompose-fam
d_tr'45'precompose'45'fam_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_tr'45'precompose'45'fam_132 = erased
-- foundation.equivalences.is-equiv-precomp-Π-is-coherently-invertible
d_is'45'equiv'45'precomp'45'Π'45'is'45'coherently'45'invertible_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'precomp'45'Π'45'is'45'coherently'45'invertible_152 ~v0
                                                                    ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_is'45'equiv'45'precomp'45'Π'45'is'45'coherently'45'invertible_152
      v6
du_is'45'equiv'45'precomp'45'Π'45'is'45'coherently'45'invertible_152 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'precomp'45'Π'45'is'45'coherently'45'invertible_152 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> case coe v2 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
               -> coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
                       (coe (\ v5 v6 -> coe v5 (coe v1 v6))) erased erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.equivalences.is-equiv-precomp-Π-is-equiv
d_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194 ~v0 ~v1 ~v2 ~v3
                                                 ~v4 v5 v6
  = du_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194 v5 v6
du_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194 v0 v1 v2
  = coe
      du_is'45'equiv'45'precomp'45'Π'45'is'45'coherently'45'invertible_152
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QpathZ45ZsplitZ45Zmaps.du_is'45'coherently'45'invertible'45'is'45'path'45'split_48
         (coe v0)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QpathZ45ZsplitZ45Zmaps.du_is'45'path'45'split'45'is'45'equiv_38
            (coe v1)))
-- foundation.equivalences.equiv-precomp-Π
d_equiv'45'precomp'45'Π_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'precomp'45'Π_218 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_equiv'45'precomp'45'Π_218 v5
du_equiv'45'precomp'45'Π_218 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'precomp'45'Π_218 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_precomp'45'Π_82
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            (coe v0)))
      (coe
         du_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            (coe v0))
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
            (coe v0))
         erased)
-- foundation.equivalences.ind-is-equiv
d_ind'45'is'45'equiv_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_ind'45'is'45'equiv_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_ind'45'is'45'equiv_248 v6 v7
du_ind'45'is'45'equiv_248 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ind'45'is'45'equiv_248 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
      (coe
         du_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194 v0 v1 erased)
-- foundation.equivalences.comp-is-equiv
d_comp'45'is'45'equiv_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'is'45'equiv_278 = erased
-- foundation.equivalences.htpy-comp-is-equiv
d_htpy'45'comp'45'is'45'equiv_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'comp'45'is'45'equiv_310 = erased
-- foundation.equivalences.is-equiv-precomp-is-equiv-precomp-Π
d_is'45'equiv'45'precomp'45'is'45'equiv'45'precomp'45'Π_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'precomp'45'is'45'equiv'45'precomp'45'Π_336 ~v0 ~v1
                                                            ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_is'45'equiv'45'precomp'45'is'45'equiv'45'precomp'45'Π_336
      v6 v7
du_is'45'equiv'45'precomp'45'is'45'equiv'45'precomp'45'Π_336 ::
  ((AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'precomp'45'is'45'equiv'45'precomp'45'Π_336 v0 v1
  = coe v0 (\ v2 -> v1)
-- foundation.equivalences.is-equiv-precomp-is-equiv
d_is'45'equiv'45'precomp'45'is'45'equiv_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'precomp'45'is'45'equiv_360 ~v0 ~v1 ~v2 ~v3 ~v4 v5
                                            v6
  = du_is'45'equiv'45'precomp'45'is'45'equiv_360 v5 v6
du_is'45'equiv'45'precomp'45'is'45'equiv_360 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'precomp'45'is'45'equiv_360 v0 v1
  = coe
      du_is'45'equiv'45'precomp'45'is'45'equiv'45'precomp'45'Π_336
      (coe
         du_is'45'equiv'45'precomp'45'Π'45'is'45'equiv_194 (coe v0)
         (coe v1))
-- foundation.equivalences.equiv-precomp
d_equiv'45'precomp_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'precomp_380 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_equiv'45'precomp_380 v5
du_equiv'45'precomp_380 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'precomp_380 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_precomp_106
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            (coe v0)))
      (coe
         du_is'45'equiv'45'precomp'45'is'45'equiv_360
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            (coe v0))
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
            (coe v0))
         erased)
-- foundation.equivalences.is-equiv-is-equiv-precomp-subuniverse
d_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.Agda.Primitive.T_Level_14) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410 v0 ~v1
                                                           ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410
      v0 v4 v7
du_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410 v0 v1
                                                            v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
               (coe v2 v0 v1) (\ v3 -> v3))))
      erased erased
-- foundation.equivalences._.is-equiv-is-equiv-precomp
d_is'45'equiv'45'is'45'equiv'45'precomp_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'equiv'45'precomp_446 v0 ~v1 v2 ~v3 v4 v5
  = du_is'45'equiv'45'is'45'equiv'45'precomp_446 v0 v2 v4 v5
du_is'45'equiv'45'is'45'equiv'45'precomp_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'equiv'45'precomp_446 v0 v1 v2 v3
  = coe
      du_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410
      (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v1) (coe v2))
      (coe
         (\ v4 v5 ->
            coe
              v3 v4
              (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                 (coe v5))))
-- foundation.equivalences.is-equiv-is-equiv-precomp-Prop
d_is'45'equiv'45'is'45'equiv'45'precomp'45'Prop_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'equiv'45'precomp'45'Prop_476 v0 ~v1 v2 ~v3
                                                    ~v4 v5
  = du_is'45'equiv'45'is'45'equiv'45'precomp'45'Prop_476 v0 v2 v5
du_is'45'equiv'45'is'45'equiv'45'precomp'45'Prop_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'equiv'45'precomp'45'Prop_476 v0 v1 v2
  = coe
      du_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410
      (coe v0) (coe v1) (coe (\ v3 -> coe v2 v3))
-- foundation.equivalences.is-equiv-is-equiv-precomp-Set
d_is'45'equiv'45'is'45'equiv'45'precomp'45'Set_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'equiv'45'precomp'45'Set_504 v0 ~v1 v2 ~v3
                                                   ~v4 v5
  = du_is'45'equiv'45'is'45'equiv'45'precomp'45'Set_504 v0 v2 v5
du_is'45'equiv'45'is'45'equiv'45'precomp'45'Set_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'equiv'45'precomp'45'Set_504 v0 v1 v2
  = coe
      du_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410
      (coe v0) (coe v1) (coe (\ v3 -> coe v2 v3))
-- foundation.equivalences.is-equiv-is-equiv-precomp-Truncated-Type
d_is'45'equiv'45'is'45'equiv'45'precomp'45'Truncated'45'Type_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'equiv'45'precomp'45'Truncated'45'Type_534 v0
                                                                 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_is'45'equiv'45'is'45'equiv'45'precomp'45'Truncated'45'Type_534
      v0 v3 v6
du_is'45'equiv'45'is'45'equiv'45'precomp'45'Truncated'45'Type_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'equiv'45'precomp'45'Truncated'45'Type_534 v0
                                                                  v1 v2
  = coe
      du_is'45'equiv'45'is'45'equiv'45'precomp'45'subuniverse_410
      (coe v0) (coe v1) (coe (\ v3 -> coe v2 v3))
-- foundation.equivalences._.is-contr-sec-is-equiv
d_is'45'contr'45'sec'45'is'45'equiv_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'sec'45'is'45'equiv_564 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_is'45'contr'45'sec'45'is'45'equiv_564 v1 v5
du_is'45'contr'45'sec'45'is'45'equiv_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'sec'45'is'45'equiv_564 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_distributive'45'Π'45'Σ_248)
      (coe
         MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_is'45'contr'45'Π_16
         (coe v0) (coe ())
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
            v1))
-- foundation.equivalences._.is-contr-retr-is-equiv
d_is'45'contr'45'retr'45'is'45'equiv_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'retr'45'is'45'equiv_586 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'contr'45'retr'45'is'45'equiv_586 v4 v5
du_is'45'contr'45'retr'45'is'45'equiv_586 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'retr'45'is'45'equiv_586 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'is'45'equiv''_206
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_tot_24
         erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
         (coe du_is'45'equiv'45'precomp'45'is'45'equiv_360 v0 v1 erased)
         (\ v2 -> v2))
-- foundation.equivalences._.is-contr-is-equiv-is-equiv
d_is'45'contr'45'is'45'equiv'45'is'45'equiv_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'equiv'45'is'45'equiv_612 ~v0 v1 ~v2 ~v3 v4
                                                v5
  = du_is'45'contr'45'is'45'equiv'45'is'45'equiv_612 v1 v4 v5
du_is'45'contr'45'is'45'equiv'45'is'45'equiv_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'equiv'45'is'45'equiv_612 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'prod_312
      (coe du_is'45'contr'45'sec'45'is'45'equiv_564 (coe v0) (coe v2))
      (coe du_is'45'contr'45'retr'45'is'45'equiv_586 (coe v1) (coe v2))
-- foundation.equivalences._.is-property-is-equiv
d_is'45'property'45'is'45'equiv_622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'property'45'is'45'equiv_622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'property'45'is'45'equiv_622
du_is'45'property'45'is'45'equiv_622 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'property'45'is'45'equiv_622 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'prop'45'is'45'contr_416
-- foundation.equivalences._.is-equiv-Prop
d_is'45'equiv'45'Prop_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Prop_636 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_is'45'equiv'45'Prop_636
du_is'45'equiv'45'Prop_636 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'Prop_636
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (\ v0 -> coe du_is'45'property'45'is'45'equiv_622)
-- foundation.equivalences._.is-emb-map-equiv
d_is'45'emb'45'map'45'equiv_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'map'45'equiv_642 ~v0 ~v1 ~v2 ~v3
  = du_is'45'emb'45'map'45'equiv_642
du_is'45'emb'45'map'45'equiv_642 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'map'45'equiv_642
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qsubtypes.du_is'45'emb'45'pr1_106
-- foundation.equivalences._.htpy-equiv
d_htpy'45'equiv_656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_htpy'45'equiv_656 = erased
-- foundation.equivalences._.extensionality-equiv
d_extensionality'45'equiv_666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_extensionality'45'equiv_666 ~v0 ~v1 ~v2 ~v3 v4
  = du_extensionality'45'equiv_666 v4
du_extensionality'45'equiv_666 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_extensionality'45'equiv_666 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QsubtypeZ45ZidentityZ45Zprinciple.du_extensionality'45'subtype_132
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe v0))
      erased
-- foundation.equivalences._.refl-htpy-equiv
d_refl'45'htpy'45'equiv_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_refl'45'htpy'45'equiv_674 = erased
-- foundation.equivalences._.is-contr-total-htpy-equiv
d_is'45'contr'45'total'45'htpy'45'equiv_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'htpy'45'equiv_680 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'contr'45'total'45'htpy'45'equiv_680 v4
du_is'45'contr'45'total'45'htpy'45'equiv_680 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'htpy'45'equiv_680 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id''_34
      (coe v0)
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
              (coe du_extensionality'45'equiv_666 v0 v1)))
-- foundation.equivalences._.eq-htpy-equiv
d_eq'45'htpy'45'equiv_692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'htpy'45'equiv_692 = erased
-- foundation.equivalences._.htpy-eq-equiv
d_htpy'45'eq'45'equiv_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'eq'45'equiv_702 = erased
-- foundation.equivalences._.Ind-htpy-equiv
d_Ind'45'htpy'45'equiv_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Ind'45'htpy'45'equiv_736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_Ind'45'htpy'45'equiv_736
du_Ind'45'htpy'45'equiv_736 ::
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Ind'45'htpy'45'equiv_736 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Zsystems.du_Ind'45'identity'45'system_56
-- foundation.equivalences._.ind-htpy-equiv
d_ind'45'htpy'45'equiv_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny
d_ind'45'htpy'45'equiv_754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ind'45'htpy'45'equiv_754
du_ind'45'htpy'45'equiv_754 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny
du_ind'45'htpy'45'equiv_754
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe du_Ind'45'htpy'45'equiv_736 erased)
-- foundation.equivalences._.comp-htpy-equiv
d_comp'45'htpy'45'equiv_772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
   ()) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'htpy'45'equiv_772 = erased
-- foundation.equivalences.associative-comp-equiv
d_associative'45'comp'45'equiv_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'comp'45'equiv_800 = erased
-- foundation.equivalences._.left-unit-law-equiv
d_left'45'unit'45'law'45'equiv_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'equiv_822 = erased
-- foundation.equivalences._.right-unit-law-equiv
d_right'45'unit'45'law'45'equiv_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'equiv_828 = erased
-- foundation.equivalences._.left-inverse-law-equiv
d_left'45'inverse'45'law'45'equiv_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'inverse'45'law'45'equiv_834 = erased
-- foundation.equivalences._.right-inverse-law-equiv
d_right'45'inverse'45'law'45'equiv_840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'inverse'45'law'45'equiv_840 = erased
-- foundation.equivalences._.inv-inv-equiv
d_inv'45'inv'45'equiv_846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_inv'45'inv'45'equiv_846 = erased
-- foundation.equivalences._.inv-inv-equiv'
d_inv'45'inv'45'equiv''_852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_inv'45'inv'45'equiv''_852 = erased
-- foundation.equivalences._.is-equiv-inv-equiv
d_is'45'equiv'45'inv'45'equiv_856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'inv'45'equiv_856 ~v0 ~v1 ~v2 ~v3
  = du_is'45'equiv'45'inv'45'equiv_856
du_is'45'equiv'45'inv'45'equiv_856 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'inv'45'equiv_856
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250)
      erased erased
-- foundation.equivalences._.equiv-inv-equiv
d_equiv'45'inv'45'equiv_858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'inv'45'equiv_858 ~v0 ~v1 ~v2 ~v3
  = du_equiv'45'inv'45'equiv_858
du_equiv'45'inv'45'equiv_858 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'inv'45'equiv_858
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250)
      (coe du_is'45'equiv'45'inv'45'equiv_856)
-- foundation.equivalences.compose-inv-equiv-compose-equiv
d_compose'45'inv'45'equiv'45'compose'45'equiv_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_compose'45'inv'45'equiv'45'compose'45'equiv_876 = erased
-- foundation.equivalences.compose-equiv-compose-inv-equiv
d_compose'45'equiv'45'compose'45'inv'45'equiv_900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_compose'45'equiv'45'compose'45'inv'45'equiv_900 = erased
-- foundation.equivalences.is-equiv-comp-equiv
d_is'45'equiv'45'comp'45'equiv_924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'comp'45'equiv_924 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_is'45'equiv'45'comp'45'equiv_924 v5
du_is'45'equiv'45'comp'45'equiv_924 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'comp'45'equiv_924 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
            (coe v0)))
      erased erased
-- foundation.equivalences.equiv-postcomp-equiv
d_equiv'45'postcomp'45'equiv_946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'postcomp'45'equiv_946 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_equiv'45'postcomp'45'equiv_946 v5
du_equiv'45'postcomp'45'equiv_946 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'postcomp'45'equiv_946 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386 v0
              v1))
      (coe du_is'45'equiv'45'comp'45'equiv_924 (coe v0))
-- foundation.equivalences.equiv-precomp-equiv
d_equiv'45'precomp'45'equiv_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'precomp'45'equiv_970 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_equiv'45'precomp'45'equiv_970 v5
du_equiv'45'precomp'45'equiv_970 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'precomp'45'equiv_970 v0
  = coe
      MAlonzo.Code.Qfoundation.Qsubtypes.du_equiv'45'subtype'45'equiv_24
      (coe du_equiv'45'precomp_380 (coe v0))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp''_370
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
                    (coe v0)))
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'left'45'factor''_500
                      (coe
                         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
                         (coe v0))
                      v2
                      (coe
                         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
                         (coe v0))))))
