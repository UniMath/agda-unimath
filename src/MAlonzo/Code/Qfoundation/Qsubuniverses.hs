{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qsubuniverses where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QsubtypeZ45ZidentityZ45Zprinciple
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qsubtypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qunivalence
import qualified MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype
import qualified MAlonzo.Code.Qfoundation.Qunivalence

-- foundation.subuniverses.is-subuniverse
d_is'45'subuniverse_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> (() -> ()) -> ()
d_is'45'subuniverse_10 = erased
-- foundation.subuniverses.subuniverse
d_subuniverse_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_subuniverse_18 = erased
-- foundation.subuniverses.is-subtype-subuniverse
d_is'45'subtype'45'subuniverse_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'subtype'45'subuniverse_32 ~v0 ~v1 v2 v3
  = du_is'45'subtype'45'subuniverse_32 v2 v3
du_is'45'subtype'45'subuniverse_32 ::
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'subtype'45'subuniverse_32 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
      (coe v0 v1)
-- foundation.subuniverses.in-subuniverse-equiv
d_in'45'subuniverse'45'equiv_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_in'45'subuniverse'45'equiv_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_in'45'subuniverse'45'equiv_48 v6
du_in'45'subuniverse'45'equiv_48 :: AgdaAny -> AgdaAny
du_in'45'subuniverse'45'equiv_48 v0 = coe v0
-- foundation.subuniverses.in-subuniverse-equiv'
d_in'45'subuniverse'45'equiv''_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_in'45'subuniverse'45'equiv''_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_in'45'subuniverse'45'equiv''_64 v6
du_in'45'subuniverse'45'equiv''_64 :: AgdaAny -> AgdaAny
du_in'45'subuniverse'45'equiv''_64 v0 = coe v0
-- foundation.subuniverses.total-subuniverse
d_total'45'subuniverse_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ()
d_total'45'subuniverse_76 = erased
-- foundation.subuniverses.is-global-subuniverse
d_is'45'global'45'subuniverse_94 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.Agda.Primitive.T_Level_14) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_is'45'global'45'subuniverse_94 = erased
-- foundation.subuniverses.equiv-subuniverse
d_equiv'45'subuniverse_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_equiv'45'subuniverse_118 = erased
-- foundation.subuniverses.equiv-eq-subuniverse
d_equiv'45'eq'45'subuniverse_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'subuniverse_136 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_equiv'45'eq'45'subuniverse_136 v3
du_equiv'45'eq'45'subuniverse_136 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'subuniverse_136 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
-- foundation.subuniverses.is-contr-total-equiv-subuniverse
d_is'45'contr'45'total'45'equiv'45'subuniverse_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv'45'subuniverse_154 ~v0 ~v1 v2 v3
  = du_is'45'contr'45'total'45'equiv'45'subuniverse_154 v2 v3
du_is'45'contr'45'total'45'equiv'45'subuniverse_154 ::
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv'45'subuniverse_154 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QsubtypeZ45ZidentityZ45Zprinciple.du_is'45'contr'45'total'45'Eq'45'subtype_30
             (coe du_is'45'subtype'45'subuniverse_32 (coe v0)) (coe v2)
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.subuniverses.is-equiv-equiv-eq-subuniverse
d_is'45'equiv'45'equiv'45'eq'45'subuniverse_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'eq'45'subuniverse_172 ~v0 ~v1 ~v2 v3
  = du_is'45'equiv'45'equiv'45'eq'45'subuniverse_172 v3
du_is'45'equiv'45'equiv'45'eq'45'subuniverse_172 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'eq'45'subuniverse_172 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
         (coe v0))
-- foundation.subuniverses.eq-equiv-subuniverse
d_eq'45'equiv'45'subuniverse_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'subuniverse_190 = erased
-- foundation.subuniverses.UU-Contr
d_UU'45'Contr_200 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_UU'45'Contr_200 = erased
-- foundation.subuniverses.type-UU-Contr
d_type'45'UU'45'Contr_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'UU'45'Contr_206 = erased
-- foundation.subuniverses.is-contr-type-UU-Contr
d_is'45'contr'45'type'45'UU'45'Contr_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'type'45'UU'45'Contr_214 ~v0 v1
  = du_is'45'contr'45'type'45'UU'45'Contr_214 v1
du_is'45'contr'45'type'45'UU'45'Contr_214 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'type'45'UU'45'Contr_214 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- foundation.subuniverses.equiv-UU-Contr
d_equiv'45'UU'45'Contr_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_equiv'45'UU'45'Contr_226 = erased
-- foundation.subuniverses.equiv-eq-UU-Contr
d_equiv'45'eq'45'UU'45'Contr_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'UU'45'Contr_238 ~v0 v1 ~v2
  = du_equiv'45'eq'45'UU'45'Contr_238 v1
du_equiv'45'eq'45'UU'45'Contr_238 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'UU'45'Contr_238 v0 v1
  = coe du_equiv'45'eq'45'subuniverse_136 (coe v0)
-- foundation.subuniverses.is-equiv-equiv-eq-UU-Contr
d_is'45'equiv'45'equiv'45'eq'45'UU'45'Contr_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'eq'45'UU'45'Contr_250 ~v0 v1 v2
  = du_is'45'equiv'45'equiv'45'eq'45'UU'45'Contr_250 v1 v2
du_is'45'equiv'45'equiv'45'eq'45'UU'45'Contr_250 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'eq'45'UU'45'Contr_250 v0 v1
  = coe du_is'45'equiv'45'equiv'45'eq'45'subuniverse_172 v0 v1
-- foundation.subuniverses.eq-equiv-UU-Contr
d_eq'45'equiv'45'UU'45'Contr_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'UU'45'Contr_262 = erased
-- foundation.subuniverses.center-UU-contr
d_center'45'UU'45'contr_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_center'45'UU'45'contr_266 ~v0 = du_center'45'UU'45'contr_266
du_center'45'UU'45'contr_266 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_center'45'UU'45'contr_266
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_is'45'contr'45'raise'45'unit_92)
-- foundation.subuniverses.contraction-UU-contr
d_contraction'45'UU'45'contr_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_contraction'45'UU'45'contr_274 = erased
-- foundation.subuniverses.is-contr-UU-Contr
d_is'45'contr'45'UU'45'Contr_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'UU'45'Contr_280 ~v0
  = du_is'45'contr'45'UU'45'Contr_280
du_is'45'contr'45'UU'45'Contr_280 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'UU'45'Contr_280
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_center'45'UU'45'contr_266) erased
-- foundation.subuniverses.UU-Trunc
d_UU'45'Trunc_288 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_UU'45'Trunc_288 = erased
-- foundation.subuniverses.type-UU-Trunc
d_type'45'UU'45'Trunc_298 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'UU'45'Trunc_298 = erased
-- foundation.subuniverses.is-trunc-type-UU-Trunc
d_is'45'trunc'45'type'45'UU'45'Trunc_308 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'trunc'45'type'45'UU'45'Trunc_308 ~v0 ~v1 v2
  = du_is'45'trunc'45'type'45'UU'45'Trunc_308 v2
du_is'45'trunc'45'type'45'UU'45'Trunc_308 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'trunc'45'type'45'UU'45'Trunc_308 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- foundation.subuniverses.is-trunc-UU-Trunc
d_is'45'trunc'45'UU'45'Trunc_316 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'trunc'45'UU'45'Trunc_316 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'is'45'equiv_184
      v0 erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qsubtypes.du_is'45'emb'45'pr1_106
         v2 v3)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'is'45'equiv_184
         v0
         (\ v4 ->
            coe MAlonzo.Code.QfoundationZ45Zcore.Qunivalence.du_equiv'45'eq_10)
         (coe
            MAlonzo.Code.Qfoundation.Qunivalence.d_univalence_10 v1 erased
            erased)
         (coe
            MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv'45'is'45'trunc_282
            (coe v1) (coe v1) (coe v0)
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
               (coe v2))
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
               (coe v3))))
