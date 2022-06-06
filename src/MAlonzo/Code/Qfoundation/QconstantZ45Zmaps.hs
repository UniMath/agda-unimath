{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QconstantZ45Zmaps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfaithfulZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZunitZ45Ztype
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.constant-maps._.fib-const
d_fib'45'const_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_fib'45'const_16 ~v0 ~v1 ~v2 ~v3 = du_fib'45'const_16
du_fib'45'const_16 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_fib'45'const_16
  = coe
      MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZunitZ45Ztype.du_left'45'unit'45'law'45'prod_62
-- foundation.constant-maps._.is-trunc-map-const-is-trunc
d_is'45'trunc'45'map'45'const'45'is'45'trunc_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'map'45'const'45'is'45'trunc_26 ~v0 ~v1 v2 v3 v4 v5
  = du_is'45'trunc'45'map'45'const'45'is'45'trunc_26 v2 v3 v4 v5
du_is'45'trunc'45'map'45'const'45'is'45'trunc_26 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'map'45'const'45'is'45'trunc_26 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv_206
      v0 (coe du_fib'45'const_16) (coe v1 v2 v3)
-- foundation.constant-maps._.is-contr-map-const-is-prop
d_is'45'contr'45'map'45'const'45'is'45'prop_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'map'45'const'45'is'45'prop_38 ~v0 ~v1
  = du_is'45'contr'45'map'45'const'45'is'45'prop_38
du_is'45'contr'45'map'45'const'45'is'45'prop_38 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'map'45'const'45'is'45'prop_38
  = coe
      du_is'45'trunc'45'map'45'const'45'is'45'trunc_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6)
-- foundation.constant-maps._.is-equiv-const-is-prop
d_is'45'equiv'45'const'45'is'45'prop_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'const'45'is'45'prop_42 ~v0 ~v1 v2 v3
  = du_is'45'equiv'45'const'45'is'45'prop_42 v2 v3
du_is'45'equiv'45'const'45'is'45'prop_42 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'const'45'is'45'prop_42 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe du_is'45'contr'45'map'45'const'45'is'45'prop_38 v0 v1)
-- foundation.constant-maps._.is-prop-map-const-is-set
d_is'45'prop'45'map'45'const'45'is'45'set_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'map'45'const'45'is'45'set_50 ~v0 ~v1
  = du_is'45'prop'45'map'45'const'45'is'45'set_50
du_is'45'prop'45'map'45'const'45'is'45'set_50 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'map'45'const'45'is'45'set_50
  = coe
      du_is'45'trunc'45'map'45'const'45'is'45'trunc_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_neg'45'one'45'𝕋_10)
-- foundation.constant-maps._.is-emb-const-is-set
d_is'45'emb'45'const'45'is'45'set_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'const'45'is'45'set_54 ~v0 ~v1 ~v2 ~v3
  = du_is'45'emb'45'const'45'is'45'set_54
du_is'45'emb'45'const'45'is'45'set_54 ::
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'const'45'is'45'set_54
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps.du_is'45'emb'45'is'45'prop'45'map_36
-- foundation.constant-maps._.is-0-map-const-is-1-type
d_is'45'0'45'map'45'const'45'is'45'1'45'type_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'0'45'map'45'const'45'is'45'1'45'type_62 ~v0 ~v1
  = du_is'45'0'45'map'45'const'45'is'45'1'45'type_62
du_is'45'0'45'map'45'const'45'is'45'1'45'type_62 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'0'45'map'45'const'45'is'45'1'45'type_62
  = coe
      du_is'45'trunc'45'map'45'const'45'is'45'trunc_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_zero'45'𝕋_12)
-- foundation.constant-maps._.is-faithful-const-is-1-type
d_is'45'faithful'45'const'45'is'45'1'45'type_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'faithful'45'const'45'is'45'1'45'type_66 ~v0 ~v1 ~v2 ~v3
  = du_is'45'faithful'45'const'45'is'45'1'45'type_66
du_is'45'faithful'45'const'45'is'45'1'45'type_66 ::
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'faithful'45'const'45'is'45'1'45'type_66 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfaithfulZ45Zmaps.du_is'45'faithful'45'is'45'0'45'map_156
-- foundation.constant-maps._.is-trunc-is-trunc-map-const
d_is'45'trunc'45'is'45'trunc'45'map'45'const_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_is'45'trunc'45'is'45'trunc'45'map'45'const_76 ~v0 ~v1 v2 v3 v4 v5
  = du_is'45'trunc'45'is'45'trunc'45'map'45'const_76 v2 v3 v4 v5
du_is'45'trunc'45'is'45'trunc'45'map'45'const_76 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_is'45'trunc'45'is'45'trunc'45'map'45'const_76 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_is'45'trunc'45'equiv''_252
      v0
      (coe
         MAlonzo.Code.Qfoundation.QtypeZ45ZarithmeticZ45ZunitZ45Ztype.du_left'45'unit'45'law'45'Σ_32)
      (coe v1 v2 v3)
-- foundation.constant-maps._.is-prop-is-contr-map-const
d_is'45'prop'45'is'45'contr'45'map'45'const_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'contr'45'map'45'const_92 ~v0 ~v1
  = du_is'45'prop'45'is'45'contr'45'map'45'const_92
du_is'45'prop'45'is'45'contr'45'map'45'const_92 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'contr'45'map'45'const_92
  = coe
      du_is'45'trunc'45'is'45'trunc'45'map'45'const_76
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6)
-- foundation.constant-maps._.is-prop-is-equiv-const
d_is'45'prop'45'is'45'equiv'45'const_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'equiv'45'const_96 ~v0 ~v1 v2
  = du_is'45'prop'45'is'45'equiv'45'const_96 v2
du_is'45'prop'45'is'45'equiv'45'const_96 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'equiv'45'const_96 v0
  = coe
      du_is'45'prop'45'is'45'contr'45'map'45'const_92
      (\ v1 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
           (coe v0 v1))
-- foundation.constant-maps._.is-set-is-prop-map-const
d_is'45'set'45'is'45'prop'45'map'45'const_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'is'45'prop'45'map'45'const_104 ~v0 ~v1
  = du_is'45'set'45'is'45'prop'45'map'45'const_104
du_is'45'set'45'is'45'prop'45'map'45'const_104 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'is'45'prop'45'map'45'const_104
  = coe
      du_is'45'trunc'45'is'45'trunc'45'map'45'const_76
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_neg'45'one'45'𝕋_10)
-- foundation.constant-maps._.is-set-is-emb-const
d_is'45'set'45'is'45'emb'45'const_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
   MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'is'45'emb'45'const_108 ~v0 ~v1 ~v2
  = du_is'45'set'45'is'45'emb'45'const_108
du_is'45'set'45'is'45'emb'45'const_108 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'is'45'emb'45'const_108
  = coe
      du_is'45'set'45'is'45'prop'45'map'45'const_104
      (\ v0 v1 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps.du_is'45'prop'45'map'45'is'45'emb_46)
-- foundation.constant-maps._.is-1-type-is-0-map-const
d_is'45'1'45'type'45'is'45'0'45'map'45'const_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'1'45'type'45'is'45'0'45'map'45'const_116 ~v0 ~v1
  = du_is'45'1'45'type'45'is'45'0'45'map'45'const_116
du_is'45'1'45'type'45'is'45'0'45'map'45'const_116 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'1'45'type'45'is'45'0'45'map'45'const_116
  = coe
      du_is'45'trunc'45'is'45'trunc'45'map'45'const_76
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_zero'45'𝕋_12)
-- foundation.constant-maps._.is-1-type-is-faithful-const
d_is'45'1'45'type'45'is'45'faithful'45'const_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
   MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'1'45'type'45'is'45'faithful'45'const_120 ~v0 ~v1 ~v2
  = du_is'45'1'45'type'45'is'45'faithful'45'const_120
du_is'45'1'45'type'45'is'45'faithful'45'const_120 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'1'45'type'45'is'45'faithful'45'const_120
  = coe
      du_is'45'1'45'type'45'is'45'0'45'map'45'const_116
      (\ v0 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QfaithfulZ45Zmaps.du_is'45'0'45'map'45'is'45'faithful_148)
-- foundation.constant-maps.const-equiv
d_const'45'equiv_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_const'45'equiv_132 ~v0 v1 v2 = du_const'45'equiv_132 v1 v2
du_const'45'equiv_132 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_const'45'equiv_132 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (\ v2 -> v1))
      (coe
         du_is'45'equiv'45'const'45'is'45'prop_42
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
            (coe v0))
         (coe v1))
-- foundation.constant-maps.const-emb
d_const'45'emb_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_const'45'emb_148 ~v0 ~v1 v2 = du_const'45'emb_148 v2
du_const'45'emb_148 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_const'45'emb_148 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (\ v1 -> v0)) (coe du_is'45'emb'45'const'45'is'45'set_54)
-- foundation.constant-maps.const-faithful-map
d_const'45'faithful'45'map_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_const'45'faithful'45'map_164 ~v0 ~v1 v2
  = du_const'45'faithful'45'map_164 v2
du_const'45'faithful'45'map_164 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_const'45'faithful'45'map_164 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (\ v1 -> v0))
      (coe du_is'45'faithful'45'const'45'is'45'1'45'type_66)
