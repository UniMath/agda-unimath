{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qslice where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qhomotopies
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Zmaps
import qualified MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple

-- foundation.slice.slice-UU
d_slice'45'UU_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_slice'45'UU_10 = erased
-- foundation.slice.Fib
d_Fib_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> ()
d_Fib_24 = erased
-- foundation.slice.Pr1
d_Pr1_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Pr1_36 ~v0 ~v1 ~v2 ~v3 = du_Pr1_36
du_Pr1_36 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Pr1_36
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26)
-- foundation.slice.hom-slice
d_hom'45'slice_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () -> () -> (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_hom'45'slice_62 = erased
-- foundation.slice.map-hom-slice
d_map'45'hom'45'slice_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'hom'45'slice_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_map'45'hom'45'slice_90 v8
du_map'45'hom'45'slice_90 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'hom'45'slice_90 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe v0)
-- foundation.slice.triangle-hom-slice
d_triangle'45'hom'45'slice_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'hom'45'slice_116 = erased
-- foundation.slice._.htpy-hom-slice
d_htpy'45'hom'45'slice_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_htpy'45'hom'45'slice_148 = erased
-- foundation.slice._.extensionality-hom-slice
d_extensionality'45'hom'45'slice_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_extensionality'45'hom'45'slice_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 v8
  = du_extensionality'45'hom'45'slice_160 v8
du_extensionality'45'hom'45'slice_160 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_extensionality'45'hom'45'slice_160 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> coe
             MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple.du_extensionality'45'Σ_138
             (coe v1) (coe v2) erased erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.slice._.eq-htpy-hom-slice
d_eq'45'htpy'45'hom'45'slice_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'htpy'45'hom'45'slice_180 = erased
-- foundation.slice.comp-hom-slice
d_comp'45'hom'45'slice_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_comp'45'hom'45'slice_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11 v12
  = du_comp'45'hom'45'slice_208 v11 v12
du_comp'45'hom'45'slice_208 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_comp'45'hom'45'slice_208 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
         (coe (\ v2 -> coe du_map'45'hom'45'slice_90 (coe v0)))
         (coe du_map'45'hom'45'slice_90 (coe v1)))
      erased
-- foundation.slice.id-hom-slice
d_id'45'hom'45'slice_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_id'45'hom'45'slice_240 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_id'45'hom'45'slice_240
du_id'45'hom'45'slice_240 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_id'45'hom'45'slice_240
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (\ v0 -> v0)) erased
-- foundation.slice.is-equiv-hom-slice
d_is'45'equiv'45'hom'45'slice_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_is'45'equiv'45'hom'45'slice_262 = erased
-- foundation.slice.fiberwise-hom-hom-slice
d_fiberwise'45'hom'45'hom'45'slice_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fiberwise'45'hom'45'hom'45'slice_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_fiberwise'45'hom'45'hom'45'slice_288 v8
du_fiberwise'45'hom'45'hom'45'slice_288 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fiberwise'45'hom'45'hom'45'slice_288 v0
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
        -> \ v3 v4 ->
             coe
               MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_fib'45'triangle_602
               (coe v1) v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.slice.hom-slice-fiberwise-hom
d_hom'45'slice'45'fiberwise'45'hom_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_hom'45'slice'45'fiberwise'45'hom_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                       ~v7 v8
  = du_hom'45'slice'45'fiberwise'45'hom_316 v6 v8
du_hom'45'slice'45'fiberwise'45'hom_316 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_hom'45'slice'45'fiberwise'45'hom_316 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         (\ v2 ->
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
              (coe
                 v1 (coe v0 v2)
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                    (coe v2) erased))))
      erased
-- foundation.slice.issec-hom-slice-fiberwise-hom-eq-htpy
d_issec'45'hom'45'slice'45'fiberwise'45'hom'45'eq'45'htpy_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'hom'45'slice'45'fiberwise'45'hom'45'eq'45'htpy_356
  = erased
-- foundation.slice.issec-hom-slice-fiberwise-hom
d_issec'45'hom'45'slice'45'fiberwise'45'hom_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'hom'45'slice'45'fiberwise'45'hom_382 = erased
-- foundation.slice.isretr-hom-slice-fiberwise-hom
d_isretr'45'hom'45'slice'45'fiberwise'45'hom_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'hom'45'slice'45'fiberwise'45'hom_408 = erased
-- foundation.slice.is-equiv-fiberwise-hom-hom-slice
d_is'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_436 ~v0 ~v1 ~v2
                                                      ~v3 ~v4 ~v5 v6 ~v7
  = du_is'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_436 v6
du_is'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_436 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_436 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_hom'45'slice'45'fiberwise'45'hom_316 (coe v0)) erased
      erased
-- foundation.slice.equiv-fiberwise-hom-hom-slice
d_equiv'45'fiberwise'45'hom'45'hom'45'slice_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'fiberwise'45'hom'45'hom'45'slice_460 ~v0 ~v1 ~v2 ~v3 ~v4
                                                ~v5 v6 ~v7
  = du_equiv'45'fiberwise'45'hom'45'hom'45'slice_460 v6
du_equiv'45'fiberwise'45'hom'45'hom'45'slice_460 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'fiberwise'45'hom'45'hom'45'slice_460 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_fiberwise'45'hom'45'hom'45'slice_288)
      (coe
         du_is'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_436 (coe v0))
-- foundation.slice.is-equiv-hom-slice-fiberwise-hom
d_is'45'equiv'45'hom'45'slice'45'fiberwise'45'hom_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'hom'45'slice'45'fiberwise'45'hom_486 ~v0 ~v1 ~v2
                                                      ~v3 ~v4 ~v5 ~v6 ~v7
  = du_is'45'equiv'45'hom'45'slice'45'fiberwise'45'hom_486
du_is'45'equiv'45'hom'45'slice'45'fiberwise'45'hom_486 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'hom'45'slice'45'fiberwise'45'hom_486
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_fiberwise'45'hom'45'hom'45'slice_288) erased erased
-- foundation.slice.equiv-hom-slice-fiberwise-hom
d_equiv'45'hom'45'slice'45'fiberwise'45'hom_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'hom'45'slice'45'fiberwise'45'hom_510 ~v0 ~v1 ~v2 ~v3 ~v4
                                                ~v5 v6 ~v7
  = du_equiv'45'hom'45'slice'45'fiberwise'45'hom_510 v6
du_equiv'45'hom'45'slice'45'fiberwise'45'hom_510 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'hom'45'slice'45'fiberwise'45'hom_510 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_hom'45'slice'45'fiberwise'45'hom_316 (coe v0))
      (coe du_is'45'equiv'45'hom'45'slice'45'fiberwise'45'hom_486)
-- foundation.slice.equiv-slice
d_equiv'45'slice_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () -> () -> (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_equiv'45'slice_536 = erased
-- foundation.slice.hom-equiv-slice
d_hom'45'equiv'45'slice_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_hom'45'equiv'45'slice_564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_hom'45'equiv'45'slice_564 v8
du_hom'45'equiv'45'slice_564 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_hom'45'equiv'45'slice_564 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
            (coe v0)))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe v0))
-- foundation.slice.is-fiberwise-equiv-fiberwise-equiv-equiv-slice
d_is'45'fiberwise'45'equiv'45'fiberwise'45'equiv'45'equiv'45'slice_596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'fiberwise'45'equiv'45'fiberwise'45'equiv'45'equiv'45'slice_596 ~v0
                                                                       ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_is'45'fiberwise'45'equiv'45'fiberwise'45'equiv'45'equiv'45'slice_596
      v6 v7 v8
du_is'45'fiberwise'45'equiv'45'fiberwise'45'equiv'45'equiv'45'slice_596 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'fiberwise'45'equiv'45'fiberwise'45'equiv'45'equiv'45'slice_596 v0
                                                                        v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'triangle_638
         (coe v0) (coe v1))
-- foundation.slice.is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
d_is'45'equiv'45'hom'45'slice'45'is'45'fiberwise'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'hom'45'slice'45'is'45'fiberwise'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_626 ~v0
                                                                                                  ~v1
                                                                                                  ~v2
                                                                                                  ~v3
                                                                                                  ~v4
                                                                                                  ~v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v8
  = du_is'45'equiv'45'hom'45'slice'45'is'45'fiberwise'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_626
      v6 v7 v8
du_is'45'equiv'45'hom'45'slice'45'is'45'fiberwise'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_626 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'hom'45'slice'45'is'45'fiberwise'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_626 v0
                                                                                                   v1
                                                                                                   v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'equiv'45'triangle'45'is'45'fiberwise'45'equiv_642
         (coe v0) (coe v1))
-- foundation.slice.equiv-fiberwise-equiv-equiv-slice
d_equiv'45'fiberwise'45'equiv'45'equiv'45'slice_654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'fiberwise'45'equiv'45'equiv'45'slice_654 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5 v6 v7
  = du_equiv'45'fiberwise'45'equiv'45'equiv'45'slice_654 v6 v7
du_equiv'45'fiberwise'45'equiv'45'equiv'45'slice_654 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'fiberwise'45'equiv'45'equiv'45'slice_654 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'Σ_544
         (coe du_equiv'45'fiberwise'45'hom'45'hom'45'slice_460 (coe v0))
         (coe du_α_666 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'right'45'swap'45'Σ_540)
-- foundation.slice._.α
d_α_666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_α_666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_α_666 v6 v7 v8
du_α_666 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_α_666 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_equiv'45'prop_154
      (coe
         du_is'45'fiberwise'45'equiv'45'fiberwise'45'equiv'45'equiv'45'slice_596
         (coe v0) (coe v1) (coe v2))
      (coe
         du_is'45'equiv'45'hom'45'slice'45'is'45'fiberwise'45'equiv'45'fiberwise'45'hom'45'hom'45'slice_626
         (coe v0) (coe v1) (coe v2))
-- foundation.slice.fiberwise-equiv-equiv-slice
d_fiberwise'45'equiv'45'equiv'45'slice_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fiberwise'45'equiv'45'equiv'45'slice_690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           v6 v7
  = du_fiberwise'45'equiv'45'equiv'45'slice_690 v6 v7
du_fiberwise'45'equiv'45'equiv'45'slice_690 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fiberwise'45'equiv'45'equiv'45'slice_690 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe
         du_equiv'45'fiberwise'45'equiv'45'equiv'45'slice_654 (coe v0)
         (coe v1))
-- foundation.slice.equiv-fam-equiv-equiv-slice
d_equiv'45'fam'45'equiv'45'equiv'45'slice_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'fam'45'equiv'45'equiv'45'slice_714 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 v6 v7
  = du_equiv'45'fam'45'equiv'45'equiv'45'slice_714 v6 v7
du_equiv'45'fam'45'equiv'45'equiv'45'slice_714 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'fam'45'equiv'45'equiv'45'slice_714 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_inv'45'distributive'45'Π'45'Σ_286)
      (coe
         du_equiv'45'fiberwise'45'equiv'45'equiv'45'slice_654 (coe v0)
         (coe v1))
-- foundation.slice.is-prop-hom-slice
d_is'45'prop'45'hom'45'slice_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'hom'45'slice_736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_is'45'prop'45'hom'45'slice_736
du_is'45'prop'45'hom'45'slice_736 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'hom'45'slice_736
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'is'45'equiv_186
-- foundation.slice.is-equiv-hom-slice-emb
d_is'45'equiv'45'hom'45'slice'45'emb_766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'hom'45'slice'45'emb_766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 ~v8 v9
  = du_is'45'equiv'45'hom'45'slice'45'emb_766 v9
du_is'45'equiv'45'hom'45'slice'45'emb_766 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'hom'45'slice'45'emb_766 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'hom'45'slice_90 (coe v0)) erased erased
-- foundation.slice._.equiv-slice'
d_equiv'45'slice''_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_equiv'45'slice''_794 = erased
-- foundation.slice._.id-equiv-slice-UU
d_id'45'equiv'45'slice'45'UU_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_id'45'equiv'45'slice'45'UU_802 ~v0 ~v1 ~v2 ~v3
  = du_id'45'equiv'45'slice'45'UU_802
du_id'45'equiv'45'slice'45'UU_802 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_id'45'equiv'45'slice'45'UU_802
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
      erased
-- foundation.slice._.equiv-eq-slice-UU
d_equiv'45'eq'45'slice'45'UU_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'slice'45'UU_812 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_equiv'45'eq'45'slice'45'UU_812
du_equiv'45'eq'45'slice'45'UU_812 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'slice'45'UU_812
  = coe du_id'45'equiv'45'slice'45'UU_802
-- foundation.slice._.is-contr-total-equiv-slice'
d_is'45'contr'45'total'45'equiv'45'slice''_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv'45'slice''_818 v0 v1 ~v2 v3
  = du_is'45'contr'45'total'45'equiv'45'slice''_818 v0 v1 v3
du_is'45'contr'45'total'45'equiv'45'slice''_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv'45'slice''_818 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
        -> coe
             MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple.du_is'45'contr'45'total'45'Eq'45'structure_34
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe v3)
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92))
             (coe
                MAlonzo.Code.Qfoundation.Qhomotopies.du_is'45'contr'45'total'45'htpy_210
                (coe v1) (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.slice._.is-equiv-equiv-eq-slice-UU
d_is'45'equiv'45'equiv'45'eq'45'slice'45'UU_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'eq'45'slice'45'UU_834 ~v0 ~v1 ~v2 v3
  = du_is'45'equiv'45'equiv'45'eq'45'slice'45'UU_834 v3
du_is'45'equiv'45'equiv'45'eq'45'slice'45'UU_834 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'eq'45'slice'45'UU_834 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.slice._.eq-equiv-slice
d_eq'45'equiv'45'slice_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'slice_842 = erased
-- foundation.slice.issec-Pr1
d_issec'45'Pr1_854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'Pr1_854 = erased
-- foundation.slice.isretr-Pr1
d_isretr'45'Pr1_864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'Pr1_864 = erased
-- foundation.slice.is-equiv-Fib
d_is'45'equiv'45'Fib_878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Fib_878 ~v0 ~v1 ~v2 = du_is'45'equiv'45'Fib_878
du_is'45'equiv'45'Fib_878 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'Fib_878
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (\ v0 -> coe du_Pr1_36) erased erased
-- foundation.slice.equiv-Fib
d_equiv'45'Fib_890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Fib_890 ~v0 ~v1 ~v2 = du_equiv'45'Fib_890
du_equiv'45'Fib_890 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Fib_890
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'equiv'45'Fib_878)
-- foundation.slice.is-equiv-Pr1
d_is'45'equiv'45'Pr1_906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Pr1_906 ~v0 ~v1 ~v2 = du_is'45'equiv'45'Pr1_906
du_is'45'equiv'45'Pr1_906 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'Pr1_906
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      erased erased erased
-- foundation.slice.equiv-Pr1
d_equiv'45'Pr1_920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Pr1_920 ~v0 ~v1 ~v2 = du_equiv'45'Pr1_920
du_equiv'45'Pr1_920 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Pr1_920
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v0 -> coe du_Pr1_36) (coe du_is'45'equiv'45'Pr1_906)
-- foundation.slice.slice-UU-structure
d_slice'45'UU'45'structure_940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> (() -> ()) -> () -> ()
d_slice'45'UU'45'structure_940 = erased
-- foundation.slice.equiv-Fib-structure
d_equiv'45'Fib'45'structure_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Fib'45'structure_960 v0 ~v1 ~v2 ~v3 ~v4
  = du_equiv'45'Fib'45'structure_960 v0
du_equiv'45'Fib'45'structure_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Fib'45'structure_960 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
         (coe
            MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_inv'45'distributive'45'Π'45'Σ_286)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'Σ_544
            (coe du_equiv'45'Fib_890)
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_equiv'45'map'45'Π_180
                    (coe v0)
                    (coe
                       (\ v2 ->
                          coe
                            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92))))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_inv'45'assoc'45'Σ_166)
-- foundation.slice.slice-UU-emb
d_slice'45'UU'45'emb_990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_slice'45'UU'45'emb_990 = erased
-- foundation.slice.equiv-Fib-Prop
d_equiv'45'Fib'45'Prop_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Fib'45'Prop_1004 ~v0 v1 ~v2
  = du_equiv'45'Fib'45'Prop_1004 v1
du_equiv'45'Fib'45'Prop_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Fib'45'Prop_1004 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe du_equiv'45'Fib'45'structure_960 (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Qfoundation.QpropositionalZ45Zmaps.du_equiv'45'is'45'prop'45'map'45'is'45'emb_48))))
