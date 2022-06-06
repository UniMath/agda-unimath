{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.QcoherentlyZ45ZinvertibleZ45Zmaps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes

-- foundation-core.coherently-invertible-maps._.has-inverse
d_has'45'inverse_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> (AgdaAny -> AgdaAny) -> ()
d_has'45'inverse_16 = erased
-- foundation-core.coherently-invertible-maps._.coherence-is-coherently-invertible
d_coherence'45'is'45'coherently'45'invertible_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  ()
d_coherence'45'is'45'coherently'45'invertible_30 = erased
-- foundation-core.coherently-invertible-maps._.is-coherently-invertible
d_is'45'coherently'45'invertible_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> (AgdaAny -> AgdaAny) -> ()
d_is'45'coherently'45'invertible_40 = erased
-- foundation-core.coherently-invertible-maps._.inv-is-coherently-invertible
d_inv'45'is'45'coherently'45'invertible_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_inv'45'is'45'coherently'45'invertible_64 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_inv'45'is'45'coherently'45'invertible_64
du_inv'45'is'45'coherently'45'invertible_64 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_inv'45'is'45'coherently'45'invertible_64
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
-- foundation-core.coherently-invertible-maps._.issec-inv-is-coherently-invertible
d_issec'45'inv'45'is'45'coherently'45'invertible_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'inv'45'is'45'coherently'45'invertible_68 = erased
-- foundation-core.coherently-invertible-maps._.isretr-inv-is-coherently-invertible
d_isretr'45'inv'45'is'45'coherently'45'invertible_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'is'45'coherently'45'invertible_74 = erased
-- foundation-core.coherently-invertible-maps._.coh-inv-is-coherently-invertible
d_coh'45'inv'45'is'45'coherently'45'invertible_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_coh'45'inv'45'is'45'coherently'45'invertible_80 = erased
-- foundation-core.coherently-invertible-maps.coh-is-coherently-invertible-id
d_coh'45'is'45'coherently'45'invertible'45'id_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_coh'45'is'45'coherently'45'invertible'45'id_96 = erased
-- foundation-core.coherently-invertible-maps._.inv-has-inverse
d_inv'45'has'45'inverse_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_inv'45'has'45'inverse_120 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inv'45'has'45'inverse_120 v5
du_inv'45'has'45'inverse_120 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_inv'45'has'45'inverse_120 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe v0)
-- foundation-core.coherently-invertible-maps._.issec-inv-has-inverse
d_issec'45'inv'45'has'45'inverse_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'inv'45'has'45'inverse_126 = erased
-- foundation-core.coherently-invertible-maps._.isretr-inv-has-inverse
d_isretr'45'inv'45'has'45'inverse_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'has'45'inverse_134 = erased
-- foundation-core.coherently-invertible-maps._.coherence-inv-has-inverse
d_coherence'45'inv'45'has'45'inverse_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_coherence'45'inv'45'has'45'inverse_140 = erased
-- foundation-core.coherently-invertible-maps._.is-coherently-invertible-has-inverse
d_is'45'coherently'45'invertible'45'has'45'inverse_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'coherently'45'invertible'45'has'45'inverse_148 ~v0 ~v1 ~v2
                                                       ~v3 ~v4 v5
  = du_is'45'coherently'45'invertible'45'has'45'inverse_148 v5
du_is'45'coherently'45'invertible'45'has'45'inverse_148 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'coherently'45'invertible'45'has'45'inverse_148 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_inv'45'has'45'inverse_120 (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         erased
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            erased erased))
