import Wire

/-!
# Bolsas y Mercados Españoles BME Equities Market And Order v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BmeBmeequitiesMarketandorderBmegateV16

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x31, 0x32]

inductive SecurityStatus where
  | active -- Active
  | inactiveProvissionalyAssumed -- Inactive Provissionaly Assumed
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .active => 0x31
  | .inactiveProvissionalyAssumed => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x31 then .active
  else .inactiveProvissionalyAssumed

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | inactiveProvissionalyAssumed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatus

/-- Exercise Style: one byte code -/
def ExerciseStyle.codes : List UInt8 :=
  [0x41, 0x45, 0x42, 0x4F]

inductive ExerciseStyle where
  | american -- American
  | european -- European
  | bermudas -- Bermudas
  | others -- Others
  | unlisted (byte : { byte : UInt8 // byte ∉ ExerciseStyle.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExerciseStyle

def toByte : ExerciseStyle → UInt8
  | .american => 0x41
  | .european => 0x45
  | .bermudas => 0x42
  | .others => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExerciseStyle :=
  if byte = 0x41 then .american
  else if byte = 0x45 then .european
  else if byte = 0x42 then .bermudas
  else .others

def ofByte (byte : UInt8) : ExerciseStyle :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExerciseStyle) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
  | bermudas => decide
  | others => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExerciseStyle) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExerciseStyle × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExerciseStyle) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExerciseStyle) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExerciseStyle) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExerciseStyle

/-- Put Or Call: one byte code -/
def PutOrCall.codes : List UInt8 :=
  [0x43, 0x50, 0x4F]

inductive PutOrCall where
  | call -- Call
  | put -- Put
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ PutOrCall.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PutOrCall

def toByte : PutOrCall → UInt8
  | .call => 0x43
  | .put => 0x50
  | .other => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PutOrCall :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .other

def ofByte (byte : UInt8) : PutOrCall :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PutOrCall) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PutOrCall) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PutOrCall × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PutOrCall) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PutOrCall) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PutOrCall) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PutOrCall

/-- Reference Trading Venue: one byte code -/
def ReferenceTradingVenue.codes : List UInt8 :=
  [0x31, 0x32, 0x34, 0x38]

inductive ReferenceTradingVenue where
  | valencia -- Valencia
  | bilbao -- Bilbao
  | barcelona -- Barcelona
  | madrid -- Madrid
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferenceTradingVenue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferenceTradingVenue

def toByte : ReferenceTradingVenue → UInt8
  | .valencia => 0x31
  | .bilbao => 0x32
  | .barcelona => 0x34
  | .madrid => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReferenceTradingVenue :=
  if byte = 0x31 then .valencia
  else if byte = 0x32 then .bilbao
  else if byte = 0x34 then .barcelona
  else .madrid

def ofByte (byte : UInt8) : ReferenceTradingVenue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferenceTradingVenue) : ofByte value.toByte = value := by
  cases value with
  | valencia => decide
  | bilbao => decide
  | barcelona => decide
  | madrid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferenceTradingVenue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferenceTradingVenue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferenceTradingVenue) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ReferenceTradingVenue) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ReferenceTradingVenue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferenceTradingVenue

/-- Settlement System: one byte code -/
def SettlementSystem.codes : List UInt8 :=
  [0x46, 0x4C]

inductive SettlementSystem where
  | iberclear -- Iberclear
  | iberclearLatibex -- Iberclear Latibex
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementSystem.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementSystem

def toByte : SettlementSystem → UInt8
  | .iberclear => 0x46
  | .iberclearLatibex => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementSystem :=
  if byte = 0x46 then .iberclear
  else .iberclearLatibex

def ofByte (byte : UInt8) : SettlementSystem :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementSystem) : ofByte value.toByte = value := by
  cases value with
  | iberclear => decide
  | iberclearLatibex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementSystem) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementSystem × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementSystem) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementSystem) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementSystem) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementSystem

/-- Nav Communication Term: one byte code -/
def NavCommunicationTerm.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive NavCommunicationTerm where
  | d1 -- D 1
  | d2 -- D 2
  | d3 -- D 3
  | unlisted (byte : { byte : UInt8 // byte ∉ NavCommunicationTerm.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NavCommunicationTerm

def toByte : NavCommunicationTerm → UInt8
  | .d1 => 0x31
  | .d2 => 0x32
  | .d3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NavCommunicationTerm :=
  if byte = 0x31 then .d1
  else if byte = 0x32 then .d2
  else .d3

def ofByte (byte : UInt8) : NavCommunicationTerm :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NavCommunicationTerm) : ofByte value.toByte = value := by
  cases value with
  | d1 => decide
  | d2 => decide
  | d3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NavCommunicationTerm) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NavCommunicationTerm × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NavCommunicationTerm) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NavCommunicationTerm) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NavCommunicationTerm) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NavCommunicationTerm

/-- Commodity Derivative Indicator: one byte code -/
def CommodityDerivativeIndicator.codes : List UInt8 :=
  [0x53, 0x4E, 0x44]

inductive CommodityDerivativeIndicator where
  | commodityDerivative -- Commodity Derivative
  | nonDerivative -- Non Derivative
  | derivative -- Derivative
  | unlisted (byte : { byte : UInt8 // byte ∉ CommodityDerivativeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CommodityDerivativeIndicator

def toByte : CommodityDerivativeIndicator → UInt8
  | .commodityDerivative => 0x53
  | .nonDerivative => 0x4E
  | .derivative => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CommodityDerivativeIndicator :=
  if byte = 0x53 then .commodityDerivative
  else if byte = 0x4E then .nonDerivative
  else .derivative

def ofByte (byte : UInt8) : CommodityDerivativeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CommodityDerivativeIndicator) : ofByte value.toByte = value := by
  cases value with
  | commodityDerivative => decide
  | nonDerivative => decide
  | derivative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CommodityDerivativeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CommodityDerivativeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CommodityDerivativeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CommodityDerivativeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CommodityDerivativeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CommodityDerivativeIndicator

/-- Exemption Situation: one byte code -/
def ExemptionSituation.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive ExemptionSituation where
  | specialistsNonExempted -- Specialists Non Exempted
  | specialistsExemptedInTheBuySide -- Specialists Exempted In The Buy Side
  | specialistsExemptedInTheSellSide -- Specialists Exempted In The Sell Side
  | specialistsExemptedInBothSidesBuyAndSell -- Specialists Exempted In Both Sides Buy And Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ ExemptionSituation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExemptionSituation

def toByte : ExemptionSituation → UInt8
  | .specialistsNonExempted => 0x30
  | .specialistsExemptedInTheBuySide => 0x31
  | .specialistsExemptedInTheSellSide => 0x32
  | .specialistsExemptedInBothSidesBuyAndSell => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExemptionSituation :=
  if byte = 0x30 then .specialistsNonExempted
  else if byte = 0x31 then .specialistsExemptedInTheBuySide
  else if byte = 0x32 then .specialistsExemptedInTheSellSide
  else .specialistsExemptedInBothSidesBuyAndSell

def ofByte (byte : UInt8) : ExemptionSituation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExemptionSituation) : ofByte value.toByte = value := by
  cases value with
  | specialistsNonExempted => decide
  | specialistsExemptedInTheBuySide => decide
  | specialistsExemptedInTheSellSide => decide
  | specialistsExemptedInBothSidesBuyAndSell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExemptionSituation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExemptionSituation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExemptionSituation) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExemptionSituation) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExemptionSituation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExemptionSituation

/-- Static Range Type: one byte code -/
def StaticRangeType.codes : List UInt8 :=
  [0x50, 0x54]

inductive StaticRangeType where
  | percentage -- Percentage
  | price -- Price
  | unlisted (byte : { byte : UInt8 // byte ∉ StaticRangeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StaticRangeType

def toByte : StaticRangeType → UInt8
  | .percentage => 0x50
  | .price => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StaticRangeType :=
  if byte = 0x50 then .percentage
  else .price

def ofByte (byte : UInt8) : StaticRangeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StaticRangeType) : ofByte value.toByte = value := by
  cases value with
  | percentage => decide
  | price => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StaticRangeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StaticRangeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StaticRangeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StaticRangeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StaticRangeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StaticRangeType

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x37, 0x3F]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | undisclosed -- Undisclosed
  | notspecified -- Notspecified
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .undisclosed => 0x37
  | .notspecified => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else if byte = 0x37 then .undisclosed
  else .notspecified

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | undisclosed => decide
  | notspecified => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x4D, 0x58, 0x54, 0x48, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36]

inductive TradeType where
  | market -- Market
  | cancellation -- Cancellation
  | tradeAmendment -- Trade Amendment
  | blockTrade -- Block Trade
  | communicatedApplication -- Communicated Application
  | authorisedApplicationTrades -- Authorised Application Trades
  | authorisedApplicationCorporateInterest -- Authorised Application Corporate Interest
  | authorisedApplicationExecutionOfContracts -- Authorised Application Execution Of Contracts
  | authorisedApplicationOtherCauses -- Authorised Application Other Causes
  | validationCommunicated -- Validation Communicated
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .market => 0x4D
  | .cancellation => 0x58
  | .tradeAmendment => 0x54
  | .blockTrade => 0x48
  | .communicatedApplication => 0x31
  | .authorisedApplicationTrades => 0x32
  | .authorisedApplicationCorporateInterest => 0x33
  | .authorisedApplicationExecutionOfContracts => 0x34
  | .authorisedApplicationOtherCauses => 0x35
  | .validationCommunicated => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x4D then .market
  else if byte = 0x58 then .cancellation
  else if byte = 0x54 then .tradeAmendment
  else if byte = 0x48 then .blockTrade
  else if byte = 0x31 then .communicatedApplication
  else if byte = 0x32 then .authorisedApplicationTrades
  else if byte = 0x33 then .authorisedApplicationCorporateInterest
  else if byte = 0x34 then .authorisedApplicationExecutionOfContracts
  else if byte = 0x35 then .authorisedApplicationOtherCauses
  else .validationCommunicated

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | cancellation => decide
  | tradeAmendment => decide
  | blockTrade => decide
  | communicatedApplication => decide
  | authorisedApplicationTrades => decide
  | authorisedApplicationCorporateInterest => decide
  | authorisedApplicationExecutionOfContracts => decide
  | authorisedApplicationOtherCauses => decide
  | validationCommunicated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Designation: one byte code -/
def Designation.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x43]

inductive Designation where
  | tradeDuringOpenMarket -- Trade During Open Market
  | tradeDuringOpeningAuction -- Trade During Opening Auction
  | tradeDuringClosingAuction -- Trade During Closing Auction
  | tradeDuringVolatilityAuction -- Trade During Volatility Auction
  | tradeDuringManualAuction -- Trade During Manual Auction
  | tradeDuringOpeningAuctionExtension -- Trade During Opening Auction Extension
  | tradeDuringClosingAuctionExtension -- Trade During Closing Auction Extension
  | tradeDuringTalPeriod -- Trade During Tal Period
  | tradeInSpainAtMidDarkBook -- Trade In Spain At Mid Dark Book
  | unlisted (byte : { byte : UInt8 // byte ∉ Designation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Designation

def toByte : Designation → UInt8
  | .tradeDuringOpenMarket => 0x31
  | .tradeDuringOpeningAuction => 0x32
  | .tradeDuringClosingAuction => 0x33
  | .tradeDuringVolatilityAuction => 0x34
  | .tradeDuringManualAuction => 0x35
  | .tradeDuringOpeningAuctionExtension => 0x36
  | .tradeDuringClosingAuctionExtension => 0x37
  | .tradeDuringTalPeriod => 0x38
  | .tradeInSpainAtMidDarkBook => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Designation :=
  if byte = 0x31 then .tradeDuringOpenMarket
  else if byte = 0x32 then .tradeDuringOpeningAuction
  else if byte = 0x33 then .tradeDuringClosingAuction
  else if byte = 0x34 then .tradeDuringVolatilityAuction
  else if byte = 0x35 then .tradeDuringManualAuction
  else if byte = 0x36 then .tradeDuringOpeningAuctionExtension
  else if byte = 0x37 then .tradeDuringClosingAuctionExtension
  else if byte = 0x38 then .tradeDuringTalPeriod
  else .tradeInSpainAtMidDarkBook

def ofByte (byte : UInt8) : Designation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Designation) : ofByte value.toByte = value := by
  cases value with
  | tradeDuringOpenMarket => decide
  | tradeDuringOpeningAuction => decide
  | tradeDuringClosingAuction => decide
  | tradeDuringVolatilityAuction => decide
  | tradeDuringManualAuction => decide
  | tradeDuringOpeningAuctionExtension => decide
  | tradeDuringClosingAuctionExtension => decide
  | tradeDuringTalPeriod => decide
  | tradeInSpainAtMidDarkBook => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Designation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Designation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Designation) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Designation) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Designation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Designation

/-- Market Mechanism: one byte code -/
def MarketMechanism.codes : List UInt8 :=
  [0x30, 0x34, 0x31, 0x35]

inductive MarketMechanism where
  | centralLimitOrderBook -- Central Limit Order Book
  | darkOrderBook -- Dark Order Book
  | offBookMessagingTrading -- Off Book Messaging Trading
  | periodicAuction -- Periodic Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMechanism.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMechanism

def toByte : MarketMechanism → UInt8
  | .centralLimitOrderBook => 0x30
  | .darkOrderBook => 0x34
  | .offBookMessagingTrading => 0x31
  | .periodicAuction => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMechanism :=
  if byte = 0x30 then .centralLimitOrderBook
  else if byte = 0x34 then .darkOrderBook
  else if byte = 0x31 then .offBookMessagingTrading
  else .periodicAuction

def ofByte (byte : UInt8) : MarketMechanism :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMechanism) : ofByte value.toByte = value := by
  cases value with
  | centralLimitOrderBook => decide
  | darkOrderBook => decide
  | offBookMessagingTrading => decide
  | periodicAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMechanism) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMechanism × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMechanism) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketMechanism) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketMechanism) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMechanism

/-- Buyer Bolsa Code: one byte code -/
def BuyerBolsaCode.codes : List UInt8 :=
  [0x33, 0x34, 0x35, 0x36]

inductive BuyerBolsaCode where
  | valencia -- Valencia
  | barcelona -- Barcelona
  | bilbao -- Bilbao
  | madrid -- Madrid
  | unlisted (byte : { byte : UInt8 // byte ∉ BuyerBolsaCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuyerBolsaCode

def toByte : BuyerBolsaCode → UInt8
  | .valencia => 0x33
  | .barcelona => 0x34
  | .bilbao => 0x35
  | .madrid => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuyerBolsaCode :=
  if byte = 0x33 then .valencia
  else if byte = 0x34 then .barcelona
  else if byte = 0x35 then .bilbao
  else .madrid

def ofByte (byte : UInt8) : BuyerBolsaCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuyerBolsaCode) : ofByte value.toByte = value := by
  cases value with
  | valencia => decide
  | barcelona => decide
  | bilbao => decide
  | madrid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuyerBolsaCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuyerBolsaCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuyerBolsaCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BuyerBolsaCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BuyerBolsaCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuyerBolsaCode

/-- Transaction Category: one byte code -/
def TransactionCategory.codes : List UInt8 :=
  [0x20, 0x44]

inductive TransactionCategory where
  | normalCategory -- Normal Category
  | darkTrade -- Dark Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionCategory

def toByte : TransactionCategory → UInt8
  | .normalCategory => 0x20
  | .darkTrade => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionCategory :=
  if byte = 0x20 then .normalCategory
  else .darkTrade

def ofByte (byte : UInt8) : TransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | normalCategory => decide
  | darkTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionCategory) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TransactionCategory) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TransactionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionCategory

/-- Bencrfpt Flag: one byte code -/
def BencrfptFlag.codes : List UInt8 :=
  [0x20, 0x36, 0x33, 0x43, 0x4D]

inductive BencrfptFlag where
  | normalTrade -- Normal Trade
  | benchmarkTradeBenc -- Benchmark Trade Benc
  | referencePriceTradeRfpt -- Reference Price Trade Rfpt
  | contingencyTradeCont -- Contingency Trade Cont
  | bencCont -- Benc Cont
  | unlisted (byte : { byte : UInt8 // byte ∉ BencrfptFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BencrfptFlag

def toByte : BencrfptFlag → UInt8
  | .normalTrade => 0x20
  | .benchmarkTradeBenc => 0x36
  | .referencePriceTradeRfpt => 0x33
  | .contingencyTradeCont => 0x43
  | .bencCont => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BencrfptFlag :=
  if byte = 0x20 then .normalTrade
  else if byte = 0x36 then .benchmarkTradeBenc
  else if byte = 0x33 then .referencePriceTradeRfpt
  else if byte = 0x43 then .contingencyTradeCont
  else .bencCont

def ofByte (byte : UInt8) : BencrfptFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BencrfptFlag) : ofByte value.toByte = value := by
  cases value with
  | normalTrade => decide
  | benchmarkTradeBenc => decide
  | referencePriceTradeRfpt => decide
  | contingencyTradeCont => decide
  | bencCont => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BencrfptFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BencrfptFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BencrfptFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BencrfptFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BencrfptFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BencrfptFlag

/-- Trade Price Condition: one byte code -/
def TradePriceCondition.codes : List UInt8 :=
  [0x20, 0x35, 0x36]

inductive TradePriceCondition where
  | plainVanillaTrade -- Plain Vanilla Trade
  | nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft -- Non Price Forming Trade Formerly Defined As A Technical Trade Npft
  | tradeNotContributingToThePriceDiscoveryProcessFormerlyDefinedAsATechnicalTradeTncpToBeDiscontinuedAsOf1StJanuary2024 -- Trade Not Contributing To The Price Discovery Process Formerly Defined As A Technical Trade Tncp To Be Discontinued As Of 1 St January 2024
  | unlisted (byte : { byte : UInt8 // byte ∉ TradePriceCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradePriceCondition

def toByte : TradePriceCondition → UInt8
  | .plainVanillaTrade => 0x20
  | .nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft => 0x35
  | .tradeNotContributingToThePriceDiscoveryProcessFormerlyDefinedAsATechnicalTradeTncpToBeDiscontinuedAsOf1StJanuary2024 => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradePriceCondition :=
  if byte = 0x20 then .plainVanillaTrade
  else if byte = 0x35 then .nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft
  else .tradeNotContributingToThePriceDiscoveryProcessFormerlyDefinedAsATechnicalTradeTncpToBeDiscontinuedAsOf1StJanuary2024

def ofByte (byte : UInt8) : TradePriceCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradePriceCondition) : ofByte value.toByte = value := by
  cases value with
  | plainVanillaTrade => decide
  | nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft => decide
  | tradeNotContributingToThePriceDiscoveryProcessFormerlyDefinedAsATechnicalTradeTncpToBeDiscontinuedAsOf1StJanuary2024 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradePriceCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradePriceCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradePriceCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradePriceCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradePriceCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradePriceCondition

/-- Pre Trade Transparency Waiver: one byte code -/
def PreTradeTransparencyWaiver.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive PreTradeTransparencyWaiver where
  | negotiatedTradeInLiquidFinancialInstrumentsNliq -- Negotiated Trade In Liquid Financial Instruments Nliq
  | negotiatedTradeInIlliquidFinancialInstrumentsOilq -- Negotiated Trade In Illiquid Financial Instruments Oilq
  | negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPricePric -- Negotiated Trade Subject To Conditions Other Than The Current Market Price Pric
  | unlisted (byte : { byte : UInt8 // byte ∉ PreTradeTransparencyWaiver.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PreTradeTransparencyWaiver

def toByte : PreTradeTransparencyWaiver → UInt8
  | .negotiatedTradeInLiquidFinancialInstrumentsNliq => 0x30
  | .negotiatedTradeInIlliquidFinancialInstrumentsOilq => 0x31
  | .negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPricePric => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PreTradeTransparencyWaiver :=
  if byte = 0x30 then .negotiatedTradeInLiquidFinancialInstrumentsNliq
  else if byte = 0x31 then .negotiatedTradeInIlliquidFinancialInstrumentsOilq
  else .negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPricePric

def ofByte (byte : UInt8) : PreTradeTransparencyWaiver :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PreTradeTransparencyWaiver) : ofByte value.toByte = value := by
  cases value with
  | negotiatedTradeInLiquidFinancialInstrumentsNliq => decide
  | negotiatedTradeInIlliquidFinancialInstrumentsOilq => decide
  | negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPricePric => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PreTradeTransparencyWaiver) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PreTradeTransparencyWaiver × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PreTradeTransparencyWaiver) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PreTradeTransparencyWaiver) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PreTradeTransparencyWaiver) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PreTradeTransparencyWaiver

/-- Deferral Waiver: one byte code -/
def DeferralWaiver.codes : List UInt8 :=
  [0x20]

inductive DeferralWaiver where
  | immediatePublication -- Immediate Publication
  | unlisted (byte : { byte : UInt8 // byte ∉ DeferralWaiver.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeferralWaiver

def toByte : DeferralWaiver → UInt8
  | .immediatePublication => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : DeferralWaiver :=
  .immediatePublication

def ofByte (byte : UInt8) : DeferralWaiver :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeferralWaiver) : ofByte value.toByte = value := by
  cases value with
  | immediatePublication => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeferralWaiver) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeferralWaiver × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeferralWaiver) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DeferralWaiver) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DeferralWaiver) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeferralWaiver

/-- Sicav Fund Counterparty Side: one byte code -/
def SicavFundCounterpartySide.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive SicavFundCounterpartySide where
  | buyer -- Buyer
  | seller -- Seller
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ SicavFundCounterpartySide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SicavFundCounterpartySide

def toByte : SicavFundCounterpartySide → UInt8
  | .buyer => 0x31
  | .seller => 0x32
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SicavFundCounterpartySide :=
  if byte = 0x31 then .buyer
  else if byte = 0x32 then .seller
  else .na

def ofByte (byte : UInt8) : SicavFundCounterpartySide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SicavFundCounterpartySide) : ofByte value.toByte = value := by
  cases value with
  | buyer => decide
  | seller => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SicavFundCounterpartySide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SicavFundCounterpartySide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SicavFundCounterpartySide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SicavFundCounterpartySide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SicavFundCounterpartySide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SicavFundCounterpartySide

/-- Amended Trade Type: one byte code -/
def AmendedTradeType.codes : List UInt8 :=
  [0x4D, 0x58, 0x54, 0x48, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36]

inductive AmendedTradeType where
  | market -- Market
  | cancellation -- Cancellation
  | tradeAmendment -- Trade Amendment
  | blockTrade -- Block Trade
  | communicatedApplication -- Communicated Application
  | authorisedApplicationTrades -- Authorised Application Trades
  | authorisedApplicationCorporateInterest -- Authorised Application Corporate Interest
  | authorisedApplicationExecutionOfContracts -- Authorised Application Execution Of Contracts
  | authorisedApplicationOtherCauses -- Authorised Application Other Causes
  | validationCommunicated -- Validation Communicated
  | unlisted (byte : { byte : UInt8 // byte ∉ AmendedTradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AmendedTradeType

def toByte : AmendedTradeType → UInt8
  | .market => 0x4D
  | .cancellation => 0x58
  | .tradeAmendment => 0x54
  | .blockTrade => 0x48
  | .communicatedApplication => 0x31
  | .authorisedApplicationTrades => 0x32
  | .authorisedApplicationCorporateInterest => 0x33
  | .authorisedApplicationExecutionOfContracts => 0x34
  | .authorisedApplicationOtherCauses => 0x35
  | .validationCommunicated => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AmendedTradeType :=
  if byte = 0x4D then .market
  else if byte = 0x58 then .cancellation
  else if byte = 0x54 then .tradeAmendment
  else if byte = 0x48 then .blockTrade
  else if byte = 0x31 then .communicatedApplication
  else if byte = 0x32 then .authorisedApplicationTrades
  else if byte = 0x33 then .authorisedApplicationCorporateInterest
  else if byte = 0x34 then .authorisedApplicationExecutionOfContracts
  else if byte = 0x35 then .authorisedApplicationOtherCauses
  else .validationCommunicated

def ofByte (byte : UInt8) : AmendedTradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AmendedTradeType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | cancellation => decide
  | tradeAmendment => decide
  | blockTrade => decide
  | communicatedApplication => decide
  | authorisedApplicationTrades => decide
  | authorisedApplicationCorporateInterest => decide
  | authorisedApplicationExecutionOfContracts => decide
  | authorisedApplicationOtherCauses => decide
  | validationCommunicated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AmendedTradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AmendedTradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AmendedTradeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AmendedTradeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AmendedTradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AmendedTradeType

/-- Last Capacity: one byte code -/
def LastCapacity.codes : List UInt8 :=
  [0x44, 0x4D, 0x41]

inductive LastCapacity where
  | dealingOnOwnAccount -- Dealing On Own Account
  | matchedPrincipal -- Matched Principal
  | anyOtherTradingCapacityBlanco -- Any Other Trading Capacity Blanco
  | unlisted (byte : { byte : UInt8 // byte ∉ LastCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastCapacity

def toByte : LastCapacity → UInt8
  | .dealingOnOwnAccount => 0x44
  | .matchedPrincipal => 0x4D
  | .anyOtherTradingCapacityBlanco => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastCapacity :=
  if byte = 0x44 then .dealingOnOwnAccount
  else if byte = 0x4D then .matchedPrincipal
  else .anyOtherTradingCapacityBlanco

def ofByte (byte : UInt8) : LastCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastCapacity) : ofByte value.toByte = value := by
  cases value with
  | dealingOnOwnAccount => decide
  | matchedPrincipal => decide
  | anyOtherTradingCapacityBlanco => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastCapacity) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastCapacity) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastCapacity

/-- Automatic Order Filter Flag: one byte code -/
def AutomaticOrderFilterFlag.codes : List UInt8 :=
  [0x32, 0x67, 0x43, 0x20]

inductive AutomaticOrderFilterFlag where
  | forOrdersEnteredByAnAuthorizedTrader -- For Orders Entered By An Authorized Trader
  | forAuthorizedArbitrationOrders -- For Authorized Arbitration Orders
  | forOrdersNotEnteredByAnAuthorizedTrader -- For Orders Not Entered By An Authorized Trader
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ AutomaticOrderFilterFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AutomaticOrderFilterFlag

def toByte : AutomaticOrderFilterFlag → UInt8
  | .forOrdersEnteredByAnAuthorizedTrader => 0x32
  | .forAuthorizedArbitrationOrders => 0x67
  | .forOrdersNotEnteredByAnAuthorizedTrader => 0x43
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AutomaticOrderFilterFlag :=
  if byte = 0x32 then .forOrdersEnteredByAnAuthorizedTrader
  else if byte = 0x67 then .forAuthorizedArbitrationOrders
  else if byte = 0x43 then .forOrdersNotEnteredByAnAuthorizedTrader
  else .na

def ofByte (byte : UInt8) : AutomaticOrderFilterFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AutomaticOrderFilterFlag) : ofByte value.toByte = value := by
  cases value with
  | forOrdersEnteredByAnAuthorizedTrader => decide
  | forAuthorizedArbitrationOrders => decide
  | forOrdersNotEnteredByAnAuthorizedTrader => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AutomaticOrderFilterFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AutomaticOrderFilterFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AutomaticOrderFilterFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AutomaticOrderFilterFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AutomaticOrderFilterFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AutomaticOrderFilterFlag

/-- Received Dept Id: one byte code -/
def ReceivedDeptId.codes : List UInt8 :=
  [0x49, 0x42, 0x54, 0x43, 0x4F, 0x20]

inductive ReceivedDeptId where
  | ordersPlacedThroughTheInternet -- Orders Placed Through The Internet
  | ordersPlacedThroughTheBankBranchNetwork -- Orders Placed Through The Bank Branch Network
  | ordersPlacedThroughAutomaticTradingSystems -- Orders Placed Through Automatic Trading Systems
  | ordersPlacedByImportantClients -- Orders Placed By Important Clients
  | others -- Others
  | naWorkstation -- Na Workstation
  | unlisted (byte : { byte : UInt8 // byte ∉ ReceivedDeptId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReceivedDeptId

def toByte : ReceivedDeptId → UInt8
  | .ordersPlacedThroughTheInternet => 0x49
  | .ordersPlacedThroughTheBankBranchNetwork => 0x42
  | .ordersPlacedThroughAutomaticTradingSystems => 0x54
  | .ordersPlacedByImportantClients => 0x43
  | .others => 0x4F
  | .naWorkstation => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReceivedDeptId :=
  if byte = 0x49 then .ordersPlacedThroughTheInternet
  else if byte = 0x42 then .ordersPlacedThroughTheBankBranchNetwork
  else if byte = 0x54 then .ordersPlacedThroughAutomaticTradingSystems
  else if byte = 0x43 then .ordersPlacedByImportantClients
  else if byte = 0x4F then .others
  else .naWorkstation

def ofByte (byte : UInt8) : ReceivedDeptId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReceivedDeptId) : ofByte value.toByte = value := by
  cases value with
  | ordersPlacedThroughTheInternet => decide
  | ordersPlacedThroughTheBankBranchNetwork => decide
  | ordersPlacedThroughAutomaticTradingSystems => decide
  | ordersPlacedByImportantClients => decide
  | others => decide
  | naWorkstation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReceivedDeptId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReceivedDeptId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReceivedDeptId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ReceivedDeptId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ReceivedDeptId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReceivedDeptId

/-- Persistence: one byte code -/
def Persistence.codes : List UInt8 :=
  [0x43, 0x50]

inductive Persistence where
  | cancelOnDisconnection -- Cancel On Disconnection
  | persistOnDisconnection -- Persist On Disconnection
  | unlisted (byte : { byte : UInt8 // byte ∉ Persistence.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Persistence

def toByte : Persistence → UInt8
  | .cancelOnDisconnection => 0x43
  | .persistOnDisconnection => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Persistence :=
  if byte = 0x43 then .cancelOnDisconnection
  else .persistOnDisconnection

def ofByte (byte : UInt8) : Persistence :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Persistence) : ofByte value.toByte = value := by
  cases value with
  | cancelOnDisconnection => decide
  | persistOnDisconnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Persistence) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Persistence × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Persistence) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Persistence) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Persistence) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Persistence

/-- Account Type: one byte code -/
def AccountType.codes : List UInt8 :=
  [0x39, 0x38, 0x41, 0x50, 0x45]

inductive AccountType where
  | retailServiceSpecialist -- Retail Service Specialist
  | retailCustomerSupportedForCompatibility -- Retail Customer Supported For Compatibility
  | onBehalfOfThirdParties -- On Behalf Of Third Parties
  | houseTrader -- House Trader
  | specialist -- Specialist
  | unlisted (byte : { byte : UInt8 // byte ∉ AccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccountType

def toByte : AccountType → UInt8
  | .retailServiceSpecialist => 0x39
  | .retailCustomerSupportedForCompatibility => 0x38
  | .onBehalfOfThirdParties => 0x41
  | .houseTrader => 0x50
  | .specialist => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AccountType :=
  if byte = 0x39 then .retailServiceSpecialist
  else if byte = 0x38 then .retailCustomerSupportedForCompatibility
  else if byte = 0x41 then .onBehalfOfThirdParties
  else if byte = 0x50 then .houseTrader
  else .specialist

def ofByte (byte : UInt8) : AccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccountType) : ofByte value.toByte = value := by
  cases value with
  | retailServiceSpecialist => decide
  | retailCustomerSupportedForCompatibility => decide
  | onBehalfOfThirdParties => decide
  | houseTrader => decide
  | specialist => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccountType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AccountType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccountType

/-- Self Match Prevention Type: one byte code -/
def SelfMatchPreventionType.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34]

inductive SelfMatchPreventionType where
  | naOrDefaultBehaviourAggressiveOrderIsRejected -- Na Or Default Behaviour Aggressive Order Is Rejected
  | rejectAggressiveOrder -- Reject Aggressive Order
  | cancelPasiveOrder -- Cancel Pasive Order
  | cancelBothPassiveAndAggressiveOrder -- Cancel Both Passive And Aggressive Order
  | noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders -- No Order Gets Cancelled Both Aggressive And Passive Orders Remain Only Valid For Spain At Mid Direct Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ SelfMatchPreventionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SelfMatchPreventionType

def toByte : SelfMatchPreventionType → UInt8
  | .naOrDefaultBehaviourAggressiveOrderIsRejected => 0x20
  | .rejectAggressiveOrder => 0x31
  | .cancelPasiveOrder => 0x32
  | .cancelBothPassiveAndAggressiveOrder => 0x33
  | .noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SelfMatchPreventionType :=
  if byte = 0x20 then .naOrDefaultBehaviourAggressiveOrderIsRejected
  else if byte = 0x31 then .rejectAggressiveOrder
  else if byte = 0x32 then .cancelPasiveOrder
  else if byte = 0x33 then .cancelBothPassiveAndAggressiveOrder
  else .noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders

def ofByte (byte : UInt8) : SelfMatchPreventionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SelfMatchPreventionType) : ofByte value.toByte = value := by
  cases value with
  | naOrDefaultBehaviourAggressiveOrderIsRejected => decide
  | rejectAggressiveOrder => decide
  | cancelPasiveOrder => decide
  | cancelBothPassiveAndAggressiveOrder => decide
  | noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SelfMatchPreventionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SelfMatchPreventionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SelfMatchPreventionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SelfMatchPreventionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SelfMatchPreventionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SelfMatchPreventionType

/-- Order Or Quote Cancel: one byte code -/
def OrderOrQuoteCancel.codes : List UInt8 :=
  [0x4E, 0x51, 0x54]

inductive OrderOrQuoteCancel where
  | ordersOnly -- Orders Only
  | quotesOnly -- Quotes Only
  | totalCancellationOrdersAndQuotes -- Total Cancellation Orders And Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderOrQuoteCancel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderOrQuoteCancel

def toByte : OrderOrQuoteCancel → UInt8
  | .ordersOnly => 0x4E
  | .quotesOnly => 0x51
  | .totalCancellationOrdersAndQuotes => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderOrQuoteCancel :=
  if byte = 0x4E then .ordersOnly
  else if byte = 0x51 then .quotesOnly
  else .totalCancellationOrdersAndQuotes

def ofByte (byte : UInt8) : OrderOrQuoteCancel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderOrQuoteCancel) : ofByte value.toByte = value := by
  cases value with
  | ordersOnly => decide
  | quotesOnly => decide
  | totalCancellationOrdersAndQuotes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderOrQuoteCancel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderOrQuoteCancel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderOrQuoteCancel) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderOrQuoteCancel) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderOrQuoteCancel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderOrQuoteCancel

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x38, 0x31, 0x32, 0x34, 0x50, 0x41, 0x53, 0x43]

inductive OrdStatus where
  | pendingNoVolumeFilled -- Pending No Volume Filled
  | rejected -- Rejected
  | parciallyFilled -- Parcially Filled
  | totallyFilled -- Totally Filled
  | cancelledNotFilled -- Cancelled Not Filled
  | cancelledPartiallyFilled -- Cancelled Partially Filled
  | nonworkingOrderPendingValidation -- Nonworking Order Pending Validation
  | nonworkingOrderPendingActivation -- Nonworking Order Pending Activation
  | expired -- Expired
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus

def toByte : OrdStatus → UInt8
  | .pendingNoVolumeFilled => 0x30
  | .rejected => 0x38
  | .parciallyFilled => 0x31
  | .totallyFilled => 0x32
  | .cancelledNotFilled => 0x34
  | .cancelledPartiallyFilled => 0x50
  | .nonworkingOrderPendingValidation => 0x41
  | .nonworkingOrderPendingActivation => 0x53
  | .expired => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .pendingNoVolumeFilled
  else if byte = 0x38 then .rejected
  else if byte = 0x31 then .parciallyFilled
  else if byte = 0x32 then .totallyFilled
  else if byte = 0x34 then .cancelledNotFilled
  else if byte = 0x50 then .cancelledPartiallyFilled
  else if byte = 0x41 then .nonworkingOrderPendingValidation
  else if byte = 0x53 then .nonworkingOrderPendingActivation
  else .expired

def ofByte (byte : UInt8) : OrdStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus) : ofByte value.toByte = value := by
  cases value with
  | pendingNoVolumeFilled => decide
  | rejected => decide
  | parciallyFilled => decide
  | totallyFilled => decide
  | cancelledNotFilled => decide
  | cancelledPartiallyFilled => decide
  | nonworkingOrderPendingValidation => decide
  | nonworkingOrderPendingActivation => decide
  | expired => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus

/-- Ord Rej Reason: one byte code -/
def OrdRejReason.codes : List UInt8 :=
  [0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x45, 0x46, 0x47, 0x48, 0x51, 0x57, 0x58, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6D, 0x78]

inductive OrdRejReason where
  | byTrader -- By Trader
  | bySupervisor -- By Supervisor
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled -- Volume Modification Incorrect New Volume Total Volume Filled
  | notExecutedImmediately -- Not Executed Immediately
  | securityNotCurrentOrNotTradeableForThisMember -- Security Not Current Or Not Tradeable For This Member
  | byLimits -- By Limits
  | cancelledByMarketStatus -- Cancelled By Market Status
  | invalidData -- Invalid Data
  | disconnectionOfTheClientApplication -- Disconnection Of The Client Application
  | quoteParametersMissing -- Quote Parameters Missing
  | byPermissions -- By Permissions
  | quoteOrClOrdIdIncorrect -- Quote Or Cl Ord Id Incorrect
  | quoteCancelledBySubstitution -- Quote Cancelled By Substitution
  | notPricesForProcessingTheOrder -- Not Prices For Processing The Order
  | byEndOfValidityOfTheOrder -- By End Of Validity Of The Order
  | other -- Other
  | notAuthorized -- Not Authorized
  | byMinimumTradingVolume -- By Minimum Trading Volume
  | priceNotAccordingToTheSizeTypology -- Price Not According To The Size Typology
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize -- The Order Volumemust Be A Multiple Of The Trading Lot Size
  | orderRejectedForTriggeringAuction -- Order Rejected For Triggering Auction
  | byQuantityToBeDisplayed -- By Quantity To Be Displayed
  | incorrectPrice -- Incorrect Price
  | incorrectVolume -- Incorrect Volume
  | incorrectDate -- Incorrect Date
  | iocOrderFailsTheAuthorizedTraderFilter -- Ioc Order Fails The Authorized Trader Filter
  | byContractStatus -- By Contract Status
  | killButton -- Kill Button
  | invalidOrkFields -- Invalid Ork Fields
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdRejReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdRejReason

def toByte : OrdRejReason → UInt8
  | .byTrader => 0x31
  | .bySupervisor => 0x33
  | .volumeModificationIncorrectNewVolumeTotalVolumeFilled => 0x34
  | .notExecutedImmediately => 0x35
  | .securityNotCurrentOrNotTradeableForThisMember => 0x36
  | .byLimits => 0x37
  | .cancelledByMarketStatus => 0x38
  | .invalidData => 0x39
  | .disconnectionOfTheClientApplication => 0x45
  | .quoteParametersMissing => 0x46
  | .byPermissions => 0x47
  | .quoteOrClOrdIdIncorrect => 0x48
  | .quoteCancelledBySubstitution => 0x51
  | .notPricesForProcessingTheOrder => 0x57
  | .byEndOfValidityOfTheOrder => 0x58
  | .other => 0x5A
  | .notAuthorized => 0x61
  | .byMinimumTradingVolume => 0x62
  | .priceNotAccordingToTheSizeTypology => 0x63
  | .theOrderVolumemustBeAMultipleOfTheTradingLotSize => 0x64
  | .orderRejectedForTriggeringAuction => 0x65
  | .byQuantityToBeDisplayed => 0x66
  | .incorrectPrice => 0x67
  | .incorrectVolume => 0x68
  | .incorrectDate => 0x69
  | .iocOrderFailsTheAuthorizedTraderFilter => 0x6A
  | .byContractStatus => 0x6B
  | .killButton => 0x6D
  | .invalidOrkFields => 0x78
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdRejReason :=
  if byte = 0x31 then .byTrader
  else if byte = 0x33 then .bySupervisor
  else if byte = 0x34 then .volumeModificationIncorrectNewVolumeTotalVolumeFilled
  else if byte = 0x35 then .notExecutedImmediately
  else if byte = 0x36 then .securityNotCurrentOrNotTradeableForThisMember
  else if byte = 0x37 then .byLimits
  else if byte = 0x38 then .cancelledByMarketStatus
  else if byte = 0x39 then .invalidData
  else if byte = 0x45 then .disconnectionOfTheClientApplication
  else if byte = 0x46 then .quoteParametersMissing
  else if byte = 0x47 then .byPermissions
  else if byte = 0x48 then .quoteOrClOrdIdIncorrect
  else if byte = 0x51 then .quoteCancelledBySubstitution
  else if byte = 0x57 then .notPricesForProcessingTheOrder
  else if byte = 0x58 then .byEndOfValidityOfTheOrder
  else if byte = 0x5A then .other
  else if byte = 0x61 then .notAuthorized
  else if byte = 0x62 then .byMinimumTradingVolume
  else if byte = 0x63 then .priceNotAccordingToTheSizeTypology
  else if byte = 0x64 then .theOrderVolumemustBeAMultipleOfTheTradingLotSize
  else if byte = 0x65 then .orderRejectedForTriggeringAuction
  else if byte = 0x66 then .byQuantityToBeDisplayed
  else if byte = 0x67 then .incorrectPrice
  else if byte = 0x68 then .incorrectVolume
  else if byte = 0x69 then .incorrectDate
  else if byte = 0x6A then .iocOrderFailsTheAuthorizedTraderFilter
  else if byte = 0x6B then .byContractStatus
  else if byte = 0x6D then .killButton
  else .invalidOrkFields

def ofByte (byte : UInt8) : OrdRejReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdRejReason) : ofByte value.toByte = value := by
  cases value with
  | byTrader => decide
  | bySupervisor => decide
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled => decide
  | notExecutedImmediately => decide
  | securityNotCurrentOrNotTradeableForThisMember => decide
  | byLimits => decide
  | cancelledByMarketStatus => decide
  | invalidData => decide
  | disconnectionOfTheClientApplication => decide
  | quoteParametersMissing => decide
  | byPermissions => decide
  | quoteOrClOrdIdIncorrect => decide
  | quoteCancelledBySubstitution => decide
  | notPricesForProcessingTheOrder => decide
  | byEndOfValidityOfTheOrder => decide
  | other => decide
  | notAuthorized => decide
  | byMinimumTradingVolume => decide
  | priceNotAccordingToTheSizeTypology => decide
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize => decide
  | orderRejectedForTriggeringAuction => decide
  | byQuantityToBeDisplayed => decide
  | incorrectPrice => decide
  | incorrectVolume => decide
  | incorrectDate => decide
  | iocOrderFailsTheAuthorizedTraderFilter => decide
  | byContractStatus => decide
  | killButton => decide
  | invalidOrkFields => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdRejReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdRejReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdRejReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdRejReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdRejReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdRejReason

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x4D, 0x47, 0x46, 0x52, 0x44, 0x38, 0x4E, 0x50, 0x56, 0x49, 0x58, 0x57]

inductive ExecType where
  | newOrderConfirmation -- New Order Confirmation
  | orderCancellation -- Order Cancellation
  | orderRefreshDueToChangeOfBook -- Order Refresh Due To Change Of Book
  | orderModification -- Order Modification
  | orderModificationDeletingIntermediatedMember -- Order Modification Deleting Intermediated Member
  | orderModificationChangingIntermediatedMember -- Order Modification Changing Intermediated Member
  | orderRefresh -- Order Refresh
  | stopOrderTriggeredAtthecloseOrderActivation -- Stop Order Triggered Attheclose Order Activation
  | orderRejection -- Order Rejection
  | orderPendingValidation -- Order Pending Validation
  | orderModificationPendingValidation -- Order Modification Pending Validation
  | orderRefreshDueToNewDisplayQty -- Order Refresh Due To New Display Qty
  | beginningOfDayOrderRefresh -- Beginning Of Day Order Refresh
  | expiredOrder -- Expired Order
  | orderStatus -- Order Status
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .newOrderConfirmation => 0x41
  | .orderCancellation => 0x42
  | .orderRefreshDueToChangeOfBook => 0x43
  | .orderModification => 0x4D
  | .orderModificationDeletingIntermediatedMember => 0x47
  | .orderModificationChangingIntermediatedMember => 0x46
  | .orderRefresh => 0x52
  | .stopOrderTriggeredAtthecloseOrderActivation => 0x44
  | .orderRejection => 0x38
  | .orderPendingValidation => 0x4E
  | .orderModificationPendingValidation => 0x50
  | .orderRefreshDueToNewDisplayQty => 0x56
  | .beginningOfDayOrderRefresh => 0x49
  | .expiredOrder => 0x58
  | .orderStatus => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x41 then .newOrderConfirmation
  else if byte = 0x42 then .orderCancellation
  else if byte = 0x43 then .orderRefreshDueToChangeOfBook
  else if byte = 0x4D then .orderModification
  else if byte = 0x47 then .orderModificationDeletingIntermediatedMember
  else if byte = 0x46 then .orderModificationChangingIntermediatedMember
  else if byte = 0x52 then .orderRefresh
  else if byte = 0x44 then .stopOrderTriggeredAtthecloseOrderActivation
  else if byte = 0x38 then .orderRejection
  else if byte = 0x4E then .orderPendingValidation
  else if byte = 0x50 then .orderModificationPendingValidation
  else if byte = 0x56 then .orderRefreshDueToNewDisplayQty
  else if byte = 0x49 then .beginningOfDayOrderRefresh
  else if byte = 0x58 then .expiredOrder
  else .orderStatus

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | newOrderConfirmation => decide
  | orderCancellation => decide
  | orderRefreshDueToChangeOfBook => decide
  | orderModification => decide
  | orderModificationDeletingIntermediatedMember => decide
  | orderModificationChangingIntermediatedMember => decide
  | orderRefresh => decide
  | stopOrderTriggeredAtthecloseOrderActivation => decide
  | orderRejection => decide
  | orderPendingValidation => decide
  | orderModificationPendingValidation => decide
  | orderRefreshDueToNewDisplayQty => decide
  | beginningOfDayOrderRefresh => decide
  | expiredOrder => decide
  | orderStatus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Ord Status 2: one byte code -/
def OrdStatus2.codes : List UInt8 :=
  [0x30, 0x38, 0x31, 0x32, 0x34, 0x50, 0x41, 0x53]

inductive OrdStatus2 where
  | pendingNoVolumeFilled -- Pending No Volume Filled
  | rejected -- Rejected
  | parciallyFilled -- Parcially Filled
  | totallyFilled -- Totally Filled
  | cancelledNotFilled -- Cancelled Not Filled
  | cancelledPartiallyFilled -- Cancelled Partially Filled
  | nonworkingOrderPendingValidation -- Nonworking Order Pending Validation
  | nonworkingOrderPendingActivation -- Nonworking Order Pending Activation
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus2

def toByte : OrdStatus2 → UInt8
  | .pendingNoVolumeFilled => 0x30
  | .rejected => 0x38
  | .parciallyFilled => 0x31
  | .totallyFilled => 0x32
  | .cancelledNotFilled => 0x34
  | .cancelledPartiallyFilled => 0x50
  | .nonworkingOrderPendingValidation => 0x41
  | .nonworkingOrderPendingActivation => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus2 :=
  if byte = 0x30 then .pendingNoVolumeFilled
  else if byte = 0x38 then .rejected
  else if byte = 0x31 then .parciallyFilled
  else if byte = 0x32 then .totallyFilled
  else if byte = 0x34 then .cancelledNotFilled
  else if byte = 0x50 then .cancelledPartiallyFilled
  else if byte = 0x41 then .nonworkingOrderPendingValidation
  else .nonworkingOrderPendingActivation

def ofByte (byte : UInt8) : OrdStatus2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus2) : ofByte value.toByte = value := by
  cases value with
  | pendingNoVolumeFilled => decide
  | rejected => decide
  | parciallyFilled => decide
  | totallyFilled => decide
  | cancelledNotFilled => decide
  | cancelledPartiallyFilled => decide
  | nonworkingOrderPendingValidation => decide
  | nonworkingOrderPendingActivation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdStatus2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdStatus2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus2

/-- Ord Rej Reason 2: one byte code -/
def OrdRejReason2.codes : List UInt8 :=
  [0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x45, 0x46, 0x47, 0x48, 0x51, 0x57, 0x58, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6D, 0x78]

inductive OrdRejReason2 where
  | byTrader -- By Trader
  | bySupervisor -- By Supervisor
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled -- Volume Modification Incorrect New Volume Total Volume Filled
  | notExecutedImmediately -- Not Executed Immediately
  | securityNotCurrentOrNotTradeableForThisMember -- Security Not Current Or Not Tradeable For This Member
  | byLimits -- By Limits
  | cancelledByMarketStatus -- Cancelled By Market Status
  | invalidData -- Invalid Data
  | disconnectionOfTheClientApplication -- Disconnection Of The Client Application
  | quoteParametersMissing -- Quote Parameters Missing
  | byPermissions -- By Permissions
  | quoteOrClOrdIdIncorrect -- Quote Or Cl Ord Id Incorrect
  | quoteCancelledBySubstitution -- Quote Cancelled By Substitution
  | notPricesForProcessingTheOrder -- Not Prices For Processing The Order
  | byEndOfValidityOfTheOrder -- By End Of Validity Of The Order
  | other -- Other
  | notAuthorized -- Not Authorized
  | byMinimumTradingVolume -- By Minimum Trading Volume
  | priceNotAccordingToTheSizeTypology -- Price Not According To The Size Typology
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize -- The Order Volumemust Be A Multiple Of The Trading Lot Size
  | orderRejectedForTriggeringAuction -- Order Rejected For Triggering Auction
  | byQuantityToBeDisplayed -- By Quantity To Be Displayed
  | incorrectPrice -- Incorrect Price
  | incorrectVolume -- Incorrect Volume
  | incorrectDate -- Incorrect Date
  | iocOrderFailsTheAuthorizedTraderFilter -- Ioc Order Fails The Authorized Trader Filter
  | byContractStatus -- By Contract Status
  | killButton -- Kill Button
  | invalidOrkFields -- Invalid Ork Fields
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdRejReason2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdRejReason2

def toByte : OrdRejReason2 → UInt8
  | .byTrader => 0x31
  | .bySupervisor => 0x33
  | .volumeModificationIncorrectNewVolumeTotalVolumeFilled => 0x34
  | .notExecutedImmediately => 0x35
  | .securityNotCurrentOrNotTradeableForThisMember => 0x36
  | .byLimits => 0x37
  | .cancelledByMarketStatus => 0x38
  | .invalidData => 0x39
  | .disconnectionOfTheClientApplication => 0x45
  | .quoteParametersMissing => 0x46
  | .byPermissions => 0x47
  | .quoteOrClOrdIdIncorrect => 0x48
  | .quoteCancelledBySubstitution => 0x51
  | .notPricesForProcessingTheOrder => 0x57
  | .byEndOfValidityOfTheOrder => 0x58
  | .other => 0x5A
  | .notAuthorized => 0x61
  | .byMinimumTradingVolume => 0x62
  | .priceNotAccordingToTheSizeTypology => 0x63
  | .theOrderVolumemustBeAMultipleOfTheTradingLotSize => 0x64
  | .orderRejectedForTriggeringAuction => 0x65
  | .byQuantityToBeDisplayed => 0x66
  | .incorrectPrice => 0x67
  | .incorrectVolume => 0x68
  | .incorrectDate => 0x69
  | .iocOrderFailsTheAuthorizedTraderFilter => 0x6A
  | .byContractStatus => 0x6B
  | .killButton => 0x6D
  | .invalidOrkFields => 0x78
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdRejReason2 :=
  if byte = 0x31 then .byTrader
  else if byte = 0x33 then .bySupervisor
  else if byte = 0x34 then .volumeModificationIncorrectNewVolumeTotalVolumeFilled
  else if byte = 0x35 then .notExecutedImmediately
  else if byte = 0x36 then .securityNotCurrentOrNotTradeableForThisMember
  else if byte = 0x37 then .byLimits
  else if byte = 0x38 then .cancelledByMarketStatus
  else if byte = 0x39 then .invalidData
  else if byte = 0x45 then .disconnectionOfTheClientApplication
  else if byte = 0x46 then .quoteParametersMissing
  else if byte = 0x47 then .byPermissions
  else if byte = 0x48 then .quoteOrClOrdIdIncorrect
  else if byte = 0x51 then .quoteCancelledBySubstitution
  else if byte = 0x57 then .notPricesForProcessingTheOrder
  else if byte = 0x58 then .byEndOfValidityOfTheOrder
  else if byte = 0x5A then .other
  else if byte = 0x61 then .notAuthorized
  else if byte = 0x62 then .byMinimumTradingVolume
  else if byte = 0x63 then .priceNotAccordingToTheSizeTypology
  else if byte = 0x64 then .theOrderVolumemustBeAMultipleOfTheTradingLotSize
  else if byte = 0x65 then .orderRejectedForTriggeringAuction
  else if byte = 0x66 then .byQuantityToBeDisplayed
  else if byte = 0x67 then .incorrectPrice
  else if byte = 0x68 then .incorrectVolume
  else if byte = 0x69 then .incorrectDate
  else if byte = 0x6A then .iocOrderFailsTheAuthorizedTraderFilter
  else if byte = 0x6B then .byContractStatus
  else if byte = 0x6D then .killButton
  else .invalidOrkFields

def ofByte (byte : UInt8) : OrdRejReason2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdRejReason2) : ofByte value.toByte = value := by
  cases value with
  | byTrader => decide
  | bySupervisor => decide
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled => decide
  | notExecutedImmediately => decide
  | securityNotCurrentOrNotTradeableForThisMember => decide
  | byLimits => decide
  | cancelledByMarketStatus => decide
  | invalidData => decide
  | disconnectionOfTheClientApplication => decide
  | quoteParametersMissing => decide
  | byPermissions => decide
  | quoteOrClOrdIdIncorrect => decide
  | quoteCancelledBySubstitution => decide
  | notPricesForProcessingTheOrder => decide
  | byEndOfValidityOfTheOrder => decide
  | other => decide
  | notAuthorized => decide
  | byMinimumTradingVolume => decide
  | priceNotAccordingToTheSizeTypology => decide
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize => decide
  | orderRejectedForTriggeringAuction => decide
  | byQuantityToBeDisplayed => decide
  | incorrectPrice => decide
  | incorrectVolume => decide
  | incorrectDate => decide
  | iocOrderFailsTheAuthorizedTraderFilter => decide
  | byContractStatus => decide
  | killButton => decide
  | invalidOrkFields => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdRejReason2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdRejReason2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdRejReason2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdRejReason2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdRejReason2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdRejReason2

/-- Exec Type 2: one byte code -/
def ExecType2.codes : List UInt8 :=
  [0x41, 0x42, 0x4D, 0x52, 0x38, 0x58, 0x57]

inductive ExecType2 where
  | newOrderConfirmation -- New Order Confirmation
  | orderCancellation -- Order Cancellation
  | orderModification -- Order Modification
  | orderRefresh -- Order Refresh
  | orderRejection -- Order Rejection
  | expiredOrder -- Expired Order
  | orderStatus -- Order Status
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType2

def toByte : ExecType2 → UInt8
  | .newOrderConfirmation => 0x41
  | .orderCancellation => 0x42
  | .orderModification => 0x4D
  | .orderRefresh => 0x52
  | .orderRejection => 0x38
  | .expiredOrder => 0x58
  | .orderStatus => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType2 :=
  if byte = 0x41 then .newOrderConfirmation
  else if byte = 0x42 then .orderCancellation
  else if byte = 0x4D then .orderModification
  else if byte = 0x52 then .orderRefresh
  else if byte = 0x38 then .orderRejection
  else if byte = 0x58 then .expiredOrder
  else .orderStatus

def ofByte (byte : UInt8) : ExecType2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType2) : ofByte value.toByte = value := by
  cases value with
  | newOrderConfirmation => decide
  | orderCancellation => decide
  | orderModification => decide
  | orderRefresh => decide
  | orderRejection => decide
  | expiredOrder => decide
  | orderStatus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecType2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecType2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType2

/-- Cxl Rej Response To: one byte code -/
def CxlRejResponseTo.codes : List UInt8 :=
  [0x31, 0x32]

inductive CxlRejResponseTo where
  | simpleOrderModification -- Simple Order Modification
  | orderCancellationRequest -- Order Cancellation Request
  | unlisted (byte : { byte : UInt8 // byte ∉ CxlRejResponseTo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CxlRejResponseTo

def toByte : CxlRejResponseTo → UInt8
  | .simpleOrderModification => 0x31
  | .orderCancellationRequest => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CxlRejResponseTo :=
  if byte = 0x31 then .simpleOrderModification
  else .orderCancellationRequest

def ofByte (byte : UInt8) : CxlRejResponseTo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CxlRejResponseTo) : ofByte value.toByte = value := by
  cases value with
  | simpleOrderModification => decide
  | orderCancellationRequest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CxlRejResponseTo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CxlRejResponseTo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CxlRejResponseTo) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CxlRejResponseTo) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CxlRejResponseTo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CxlRejResponseTo

/-- Cxl Rej Reason: one byte code -/
def CxlRejReason.codes : List UInt8 :=
  [0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x45, 0x46, 0x47, 0x48, 0x51, 0x57, 0x58, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6D, 0x78]

inductive CxlRejReason where
  | byTrader -- By Trader
  | bySupervisor -- By Supervisor
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled -- Volume Modification Incorrect New Volume Total Volume Filled
  | notExecutedImmediately -- Not Executed Immediately
  | securityNotCurrentOrNotTradeableForThisMember -- Security Not Current Or Not Tradeable For This Member
  | byLimits -- By Limits
  | cancelledByMarketStatus -- Cancelled By Market Status
  | invalidData -- Invalid Data
  | disconnectionOfTheClientApplication -- Disconnection Of The Client Application
  | quoteParametersMissing -- Quote Parameters Missing
  | byPermissions -- By Permissions
  | quoteOrClOrdIdIncorrect -- Quote Or Cl Ord Id Incorrect
  | quoteCancelledBySubstitution -- Quote Cancelled By Substitution
  | notPricesForProcessingTheOrder -- Not Prices For Processing The Order
  | byEndOfValidityOfTheOrder -- By End Of Validity Of The Order
  | other -- Other
  | notAuthorized -- Not Authorized
  | byMinimumTradingVolume -- By Minimum Trading Volume
  | priceNotAccordingToTheSizeTypology -- Price Not According To The Size Typology
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize -- The Order Volumemust Be A Multiple Of The Trading Lot Size
  | orderRejectedForTriggeringAuction -- Order Rejected For Triggering Auction
  | byQuantityToBeDisplayed -- By Quantity To Be Displayed
  | incorrectPrice -- Incorrect Price
  | incorrectVolume -- Incorrect Volume
  | incorrectDate -- Incorrect Date
  | iocOrderFailsTheAuthorizedTraderFilter -- Ioc Order Fails The Authorized Trader Filter
  | byContractStatus -- By Contract Status
  | killButton -- Kill Button
  | invalidOrkFields -- Invalid Ork Fields
  | unlisted (byte : { byte : UInt8 // byte ∉ CxlRejReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CxlRejReason

def toByte : CxlRejReason → UInt8
  | .byTrader => 0x31
  | .bySupervisor => 0x33
  | .volumeModificationIncorrectNewVolumeTotalVolumeFilled => 0x34
  | .notExecutedImmediately => 0x35
  | .securityNotCurrentOrNotTradeableForThisMember => 0x36
  | .byLimits => 0x37
  | .cancelledByMarketStatus => 0x38
  | .invalidData => 0x39
  | .disconnectionOfTheClientApplication => 0x45
  | .quoteParametersMissing => 0x46
  | .byPermissions => 0x47
  | .quoteOrClOrdIdIncorrect => 0x48
  | .quoteCancelledBySubstitution => 0x51
  | .notPricesForProcessingTheOrder => 0x57
  | .byEndOfValidityOfTheOrder => 0x58
  | .other => 0x5A
  | .notAuthorized => 0x61
  | .byMinimumTradingVolume => 0x62
  | .priceNotAccordingToTheSizeTypology => 0x63
  | .theOrderVolumemustBeAMultipleOfTheTradingLotSize => 0x64
  | .orderRejectedForTriggeringAuction => 0x65
  | .byQuantityToBeDisplayed => 0x66
  | .incorrectPrice => 0x67
  | .incorrectVolume => 0x68
  | .incorrectDate => 0x69
  | .iocOrderFailsTheAuthorizedTraderFilter => 0x6A
  | .byContractStatus => 0x6B
  | .killButton => 0x6D
  | .invalidOrkFields => 0x78
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CxlRejReason :=
  if byte = 0x31 then .byTrader
  else if byte = 0x33 then .bySupervisor
  else if byte = 0x34 then .volumeModificationIncorrectNewVolumeTotalVolumeFilled
  else if byte = 0x35 then .notExecutedImmediately
  else if byte = 0x36 then .securityNotCurrentOrNotTradeableForThisMember
  else if byte = 0x37 then .byLimits
  else if byte = 0x38 then .cancelledByMarketStatus
  else if byte = 0x39 then .invalidData
  else if byte = 0x45 then .disconnectionOfTheClientApplication
  else if byte = 0x46 then .quoteParametersMissing
  else if byte = 0x47 then .byPermissions
  else if byte = 0x48 then .quoteOrClOrdIdIncorrect
  else if byte = 0x51 then .quoteCancelledBySubstitution
  else if byte = 0x57 then .notPricesForProcessingTheOrder
  else if byte = 0x58 then .byEndOfValidityOfTheOrder
  else if byte = 0x5A then .other
  else if byte = 0x61 then .notAuthorized
  else if byte = 0x62 then .byMinimumTradingVolume
  else if byte = 0x63 then .priceNotAccordingToTheSizeTypology
  else if byte = 0x64 then .theOrderVolumemustBeAMultipleOfTheTradingLotSize
  else if byte = 0x65 then .orderRejectedForTriggeringAuction
  else if byte = 0x66 then .byQuantityToBeDisplayed
  else if byte = 0x67 then .incorrectPrice
  else if byte = 0x68 then .incorrectVolume
  else if byte = 0x69 then .incorrectDate
  else if byte = 0x6A then .iocOrderFailsTheAuthorizedTraderFilter
  else if byte = 0x6B then .byContractStatus
  else if byte = 0x6D then .killButton
  else .invalidOrkFields

def ofByte (byte : UInt8) : CxlRejReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CxlRejReason) : ofByte value.toByte = value := by
  cases value with
  | byTrader => decide
  | bySupervisor => decide
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled => decide
  | notExecutedImmediately => decide
  | securityNotCurrentOrNotTradeableForThisMember => decide
  | byLimits => decide
  | cancelledByMarketStatus => decide
  | invalidData => decide
  | disconnectionOfTheClientApplication => decide
  | quoteParametersMissing => decide
  | byPermissions => decide
  | quoteOrClOrdIdIncorrect => decide
  | quoteCancelledBySubstitution => decide
  | notPricesForProcessingTheOrder => decide
  | byEndOfValidityOfTheOrder => decide
  | other => decide
  | notAuthorized => decide
  | byMinimumTradingVolume => decide
  | priceNotAccordingToTheSizeTypology => decide
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize => decide
  | orderRejectedForTriggeringAuction => decide
  | byQuantityToBeDisplayed => decide
  | incorrectPrice => decide
  | incorrectVolume => decide
  | incorrectDate => decide
  | iocOrderFailsTheAuthorizedTraderFilter => decide
  | byContractStatus => decide
  | killButton => decide
  | invalidOrkFields => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CxlRejReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CxlRejReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CxlRejReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CxlRejReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CxlRejReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CxlRejReason

/-- Mass Cancel Reject Reason: one byte code -/
def MassCancelRejectReason.codes : List UInt8 :=
  [0x47, 0x38, 0x39]

inductive MassCancelRejectReason where
  | noPermission -- No Permission
  | cancelledBecauseOfMarketState -- Cancelled Because Of Market State
  | invalidData -- Invalid Data
  | unlisted (byte : { byte : UInt8 // byte ∉ MassCancelRejectReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MassCancelRejectReason

def toByte : MassCancelRejectReason → UInt8
  | .noPermission => 0x47
  | .cancelledBecauseOfMarketState => 0x38
  | .invalidData => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MassCancelRejectReason :=
  if byte = 0x47 then .noPermission
  else if byte = 0x38 then .cancelledBecauseOfMarketState
  else .invalidData

def ofByte (byte : UInt8) : MassCancelRejectReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MassCancelRejectReason) : ofByte value.toByte = value := by
  cases value with
  | noPermission => decide
  | cancelledBecauseOfMarketState => decide
  | invalidData => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MassCancelRejectReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MassCancelRejectReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MassCancelRejectReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MassCancelRejectReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MassCancelRejectReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MassCancelRejectReason

/-- Ccp Code: one byte code -/
def CcpCode.codes : List UInt8 :=
  [0x30, 0x31]

inductive CcpCode where
  | na -- Na
  | bmeClearingOthersToBeDefined -- Bme Clearing… Others To Be Defined
  | unlisted (byte : { byte : UInt8 // byte ∉ CcpCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CcpCode

def toByte : CcpCode → UInt8
  | .na => 0x30
  | .bmeClearingOthersToBeDefined => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CcpCode :=
  if byte = 0x30 then .na
  else .bmeClearingOthersToBeDefined

def ofByte (byte : UInt8) : CcpCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CcpCode) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | bmeClearingOthersToBeDefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CcpCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CcpCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CcpCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CcpCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CcpCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CcpCode

/-- Aggressor Indicator: one byte code -/
def AggressorIndicator.codes : List UInt8 :=
  [0x20, 0x50, 0x41]

inductive AggressorIndicator where
  | na -- Na
  | passive -- Passive
  | aggresive -- Aggresive
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressorIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressorIndicator

def toByte : AggressorIndicator → UInt8
  | .na => 0x20
  | .passive => 0x50
  | .aggresive => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressorIndicator :=
  if byte = 0x20 then .na
  else if byte = 0x50 then .passive
  else .aggresive

def ofByte (byte : UInt8) : AggressorIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressorIndicator) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | passive => decide
  | aggresive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AggressorIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AggressorIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AggressorIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AggressorIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AggressorIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AggressorIndicator

/-- Ccp Code 2: one byte code -/
def CcpCode2.codes : List UInt8 :=
  [0x30, 0x31]

inductive CcpCode2 where
  | na -- Na
  | bmeClearingOthersToBeDefined -- Bme Clearing… Others To Be Defined
  | unlisted (byte : { byte : UInt8 // byte ∉ CcpCode2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CcpCode2

def toByte : CcpCode2 → UInt8
  | .na => 0x30
  | .bmeClearingOthersToBeDefined => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CcpCode2 :=
  if byte = 0x30 then .na
  else .bmeClearingOthersToBeDefined

def ofByte (byte : UInt8) : CcpCode2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CcpCode2) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | bmeClearingOthersToBeDefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CcpCode2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CcpCode2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CcpCode2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CcpCode2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CcpCode2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CcpCode2

/-- Aggressor Indicator 2: one byte code -/
def AggressorIndicator2.codes : List UInt8 :=
  [0x20, 0x50, 0x41]

inductive AggressorIndicator2 where
  | na -- Na
  | passive -- Passive
  | aggressive -- Aggressive
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressorIndicator2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressorIndicator2

def toByte : AggressorIndicator2 → UInt8
  | .na => 0x20
  | .passive => 0x50
  | .aggressive => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressorIndicator2 :=
  if byte = 0x20 then .na
  else if byte = 0x50 then .passive
  else .aggressive

def ofByte (byte : UInt8) : AggressorIndicator2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressorIndicator2) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | passive => decide
  | aggressive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AggressorIndicator2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AggressorIndicator2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AggressorIndicator2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AggressorIndicator2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AggressorIndicator2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AggressorIndicator2

/-- Last Capacity 2: one byte code -/
def LastCapacity2.codes : List UInt8 :=
  [0x44, 0x4D, 0x41]

inductive LastCapacity2 where
  | dealingOnOwnAccount -- Dealing On Own Account
  | matchedPrincipal -- Matched Principal
  | anyOtherTradingCapacityBlanco -- Any Other Trading Capacity Blanco
  | unlisted (byte : { byte : UInt8 // byte ∉ LastCapacity2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastCapacity2

def toByte : LastCapacity2 → UInt8
  | .dealingOnOwnAccount => 0x44
  | .matchedPrincipal => 0x4D
  | .anyOtherTradingCapacityBlanco => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastCapacity2 :=
  if byte = 0x44 then .dealingOnOwnAccount
  else if byte = 0x4D then .matchedPrincipal
  else .anyOtherTradingCapacityBlanco

def ofByte (byte : UInt8) : LastCapacity2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastCapacity2) : ofByte value.toByte = value := by
  cases value with
  | dealingOnOwnAccount => decide
  | matchedPrincipal => decide
  | anyOtherTradingCapacityBlanco => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastCapacity2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastCapacity2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastCapacity2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastCapacity2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastCapacity2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastCapacity2

/-- Automatic Order Filter Flag 2: one byte code -/
def AutomaticOrderFilterFlag2.codes : List UInt8 :=
  [0x32, 0x67, 0x43, 0x20]

inductive AutomaticOrderFilterFlag2 where
  | forOrdersEnteredByAnAuthorizedTrader -- For Orders Entered By An Authorized Trader
  | forAuthorizedArbitrationOrders -- For Authorized Arbitration Orders
  | forOrdersNotEnteredByAnAuthorizedTrader -- For Orders Not Entered By An Authorized Trader
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ AutomaticOrderFilterFlag2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AutomaticOrderFilterFlag2

def toByte : AutomaticOrderFilterFlag2 → UInt8
  | .forOrdersEnteredByAnAuthorizedTrader => 0x32
  | .forAuthorizedArbitrationOrders => 0x67
  | .forOrdersNotEnteredByAnAuthorizedTrader => 0x43
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AutomaticOrderFilterFlag2 :=
  if byte = 0x32 then .forOrdersEnteredByAnAuthorizedTrader
  else if byte = 0x67 then .forAuthorizedArbitrationOrders
  else if byte = 0x43 then .forOrdersNotEnteredByAnAuthorizedTrader
  else .na

def ofByte (byte : UInt8) : AutomaticOrderFilterFlag2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AutomaticOrderFilterFlag2) : ofByte value.toByte = value := by
  cases value with
  | forOrdersEnteredByAnAuthorizedTrader => decide
  | forAuthorizedArbitrationOrders => decide
  | forOrdersNotEnteredByAnAuthorizedTrader => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AutomaticOrderFilterFlag2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AutomaticOrderFilterFlag2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AutomaticOrderFilterFlag2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AutomaticOrderFilterFlag2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AutomaticOrderFilterFlag2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AutomaticOrderFilterFlag2

/-- Received Dept Id 2: one byte code -/
def ReceivedDeptId2.codes : List UInt8 :=
  [0x49, 0x42, 0x54, 0x43, 0x4F, 0x20]

inductive ReceivedDeptId2 where
  | ordersPlacedThroughTheInternet -- Orders Placed Through The Internet
  | ordersPlacedThroughTheBankBranchNetwork -- Orders Placed Through The Bank Branch Network
  | ordersPlacedThroughAutomaticTradingSystems -- Orders Placed Through Automatic Trading Systems
  | ordersPlacedByImportantClients -- Orders Placed By Important Clients
  | others -- Others
  | naWorkstation -- Na Workstation
  | unlisted (byte : { byte : UInt8 // byte ∉ ReceivedDeptId2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReceivedDeptId2

def toByte : ReceivedDeptId2 → UInt8
  | .ordersPlacedThroughTheInternet => 0x49
  | .ordersPlacedThroughTheBankBranchNetwork => 0x42
  | .ordersPlacedThroughAutomaticTradingSystems => 0x54
  | .ordersPlacedByImportantClients => 0x43
  | .others => 0x4F
  | .naWorkstation => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReceivedDeptId2 :=
  if byte = 0x49 then .ordersPlacedThroughTheInternet
  else if byte = 0x42 then .ordersPlacedThroughTheBankBranchNetwork
  else if byte = 0x54 then .ordersPlacedThroughAutomaticTradingSystems
  else if byte = 0x43 then .ordersPlacedByImportantClients
  else if byte = 0x4F then .others
  else .naWorkstation

def ofByte (byte : UInt8) : ReceivedDeptId2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReceivedDeptId2) : ofByte value.toByte = value := by
  cases value with
  | ordersPlacedThroughTheInternet => decide
  | ordersPlacedThroughTheBankBranchNetwork => decide
  | ordersPlacedThroughAutomaticTradingSystems => decide
  | ordersPlacedByImportantClients => decide
  | others => decide
  | naWorkstation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReceivedDeptId2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReceivedDeptId2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReceivedDeptId2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ReceivedDeptId2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ReceivedDeptId2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReceivedDeptId2

/-- Persistence 2: one byte code -/
def Persistence2.codes : List UInt8 :=
  [0x43, 0x50]

inductive Persistence2 where
  | cancelOnDisconnection -- Cancel On Disconnection
  | persistOnDisconnection -- Persist On Disconnection
  | unlisted (byte : { byte : UInt8 // byte ∉ Persistence2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Persistence2

def toByte : Persistence2 → UInt8
  | .cancelOnDisconnection => 0x43
  | .persistOnDisconnection => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Persistence2 :=
  if byte = 0x43 then .cancelOnDisconnection
  else .persistOnDisconnection

def ofByte (byte : UInt8) : Persistence2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Persistence2) : ofByte value.toByte = value := by
  cases value with
  | cancelOnDisconnection => decide
  | persistOnDisconnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Persistence2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Persistence2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Persistence2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Persistence2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Persistence2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Persistence2

/-- Account Type 2: one byte code -/
def AccountType2.codes : List UInt8 :=
  [0x39, 0x41, 0x50, 0x45]

inductive AccountType2 where
  | retailServiceSpecialist -- Retail Service Specialist
  | onBehalfOfThirdParties -- On Behalf Of Third Parties
  | houseTrader -- House Trader
  | specialist -- Specialist
  | unlisted (byte : { byte : UInt8 // byte ∉ AccountType2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccountType2

def toByte : AccountType2 → UInt8
  | .retailServiceSpecialist => 0x39
  | .onBehalfOfThirdParties => 0x41
  | .houseTrader => 0x50
  | .specialist => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AccountType2 :=
  if byte = 0x39 then .retailServiceSpecialist
  else if byte = 0x41 then .onBehalfOfThirdParties
  else if byte = 0x50 then .houseTrader
  else .specialist

def ofByte (byte : UInt8) : AccountType2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccountType2) : ofByte value.toByte = value := by
  cases value with
  | retailServiceSpecialist => decide
  | onBehalfOfThirdParties => decide
  | houseTrader => decide
  | specialist => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccountType2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccountType2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccountType2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AccountType2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AccountType2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccountType2

/-- Self Match Prevention Type 2: one byte code -/
def SelfMatchPreventionType2.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34]

inductive SelfMatchPreventionType2 where
  | naOrDefaultBehaviourAggressiveOrderIsRejected -- Na Or Default Behaviour Aggressive Order Is Rejected
  | rejectAggressiveOrder -- Reject Aggressive Order
  | cancel139AssiveOrder -- Cancel 139 Assive Order
  | cancelBothPassiveAndAggressiveOrder -- Cancel Both Passive And Aggressive Order
  | noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders -- No Order Gets Cancelled Both Aggressive And Passive Orders Remain Only Valid For Spain At Mid Direct Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ SelfMatchPreventionType2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SelfMatchPreventionType2

def toByte : SelfMatchPreventionType2 → UInt8
  | .naOrDefaultBehaviourAggressiveOrderIsRejected => 0x20
  | .rejectAggressiveOrder => 0x31
  | .cancel139AssiveOrder => 0x32
  | .cancelBothPassiveAndAggressiveOrder => 0x33
  | .noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SelfMatchPreventionType2 :=
  if byte = 0x20 then .naOrDefaultBehaviourAggressiveOrderIsRejected
  else if byte = 0x31 then .rejectAggressiveOrder
  else if byte = 0x32 then .cancel139AssiveOrder
  else if byte = 0x33 then .cancelBothPassiveAndAggressiveOrder
  else .noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders

def ofByte (byte : UInt8) : SelfMatchPreventionType2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SelfMatchPreventionType2) : ofByte value.toByte = value := by
  cases value with
  | naOrDefaultBehaviourAggressiveOrderIsRejected => decide
  | rejectAggressiveOrder => decide
  | cancel139AssiveOrder => decide
  | cancelBothPassiveAndAggressiveOrder => decide
  | noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SelfMatchPreventionType2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SelfMatchPreventionType2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SelfMatchPreventionType2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SelfMatchPreventionType2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SelfMatchPreventionType2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SelfMatchPreventionType2

/-- Logon Response Message: 26 bytes -/
structure LogonResponseMessage where
  sequenceNumber : BitVec 32
  heartBtInt : BitVec 8
  protocolVersion : Alpha 6
  testProductionInd : Alpha 1
  environmentCode : Alpha 2
  sessionDate : BitVec 32
  expectedSequenceNumber : BitVec 32
  sequenceNumberTo : BitVec 32
  deriving DecidableEq, Repr

namespace LogonResponseMessage

def encode (message : LogonResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.heartBtInt
    ++ (Alpha.encode message.protocolVersion
    ++ (Alpha.encode message.testProductionInd
    ++ (Alpha.encode message.environmentCode
    ++ (encodeUIntLE 4 message.sessionDate
    ++ (encodeUIntLE 4 message.expectedSequenceNumber
    ++ (encodeUIntLE 4 message.sequenceNumberTo)))))))

def decode (bytes : List UInt8) : Option (LogonResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (heartBtInt, bytes) ← decodeUIntLE 1 bytes
  let (protocolVersion, bytes) ← Alpha.decode 6 bytes
  let (testProductionInd, bytes) ← Alpha.decode 1 bytes
  let (environmentCode, bytes) ← Alpha.decode 2 bytes
  let (sessionDate, bytes) ← decodeUIntLE 4 bytes
  let (expectedSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumberTo, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, heartBtInt, protocolVersion, testProductionInd, environmentCode, sessionDate, expectedSequenceNumber, sequenceNumberTo }, bytes)

@[simp] theorem encode_length (message : LogonResponseMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonResponseMessage

/-- Logout Response Message: 5 bytes -/
structure LogoutResponseMessage where
  sequenceNumber : BitVec 32
  logoutReason : BitVec 8
  deriving DecidableEq, Repr

namespace LogoutResponseMessage

def encode (message : LogoutResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.logoutReason)

def decode (bytes : List UInt8) : Option (LogoutResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (logoutReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, logoutReason }, bytes)

@[simp] theorem encode_length (message : LogoutResponseMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LogoutResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogoutResponseMessage

/-- Heartbeat Message: 4 bytes -/
structure HeartbeatMessage where
  sequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HeartbeatMessage

/-- Network Status Message: 5 bytes -/
structure NetworkStatusMessage where
  sequenceNumber : BitVec 32
  networkStatusValue : BitVec 8
  deriving DecidableEq, Repr

namespace NetworkStatusMessage

def encode (message : NetworkStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.networkStatusValue)

def decode (bytes : List UInt8) : Option (NetworkStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (networkStatusValue, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, networkStatusValue }, bytes)

@[simp] theorem encode_length (message : NetworkStatusMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NetworkStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetworkStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NetworkStatusMessage

/-- Logon Message: 53 bytes -/
structure LogonMessage where
  username : Alpha 7
  password : Alpha 10
  softwareName : Alpha 25
  expectedSequenceNumber : BitVec 32
  subscriptions : BitVec 8
  protocolVersion : Alpha 6
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.softwareName
    ++ (encodeUIntLE 4 message.expectedSequenceNumber
    ++ (encodeUIntLE 1 message.subscriptions
    ++ (Alpha.encode message.protocolVersion)))))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 7 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (softwareName, bytes) ← Alpha.decode 25 bytes
  let (expectedSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (subscriptions, bytes) ← decodeUIntLE 1 bytes
  let (protocolVersion, bytes) ← Alpha.decode 6 bytes
  pure ({ username, password, softwareName, expectedSequenceNumber, subscriptions, protocolVersion }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Reject Message: 70 bytes -/
structure RejectMessage where
  sequenceNumber : BitVec 32
  sessionRejectReason : BitVec 8
  textC58 : Alpha 58
  msgRejectedReference : Alpha 7
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.sessionRejectReason
    ++ (Alpha.encode message.textC58
    ++ (Alpha.encode message.msgRejectedReference)))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 1 bytes
  let (textC58, bytes) ← Alpha.decode 58 bytes
  let (msgRejectedReference, bytes) ← Alpha.decode 7 bytes
  pure ({ sequenceNumber, sessionRejectReason, textC58, msgRejectedReference }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RejectMessage

/-- Trading Session Status Message: 15 bytes -/
structure TradingSessionStatusMessage where
  sequenceNumber : BitVec 32
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  transactionDateAndTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 1 message.tradingSessionSubId
    ++ (encodeUIntLE 1 message.tradSesStatus
    ++ (encodeUIntLE 8 message.transactionDateAndTime))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUIntLE 1 bytes
  let (tradSesStatus, bytes) ← decodeUIntLE 1 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, tradingSessionId, tradingSessionSubId, tradSesStatus, transactionDateAndTime }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatusMessage

/-- News Message: 82 bytes -/
structure NewsMessage where
  sequenceNumber : BitVec 32
  newsText : Alpha 78
  deriving DecidableEq, Repr

namespace NewsMessage

def encode (message : NewsMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.newsText)

def decode (bytes : List UInt8) : Option (NewsMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (newsText, bytes) ← Alpha.decode 78 bytes
  pure ({ sequenceNumber, newsText }, bytes)

@[simp] theorem encode_length (message : NewsMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : NewsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsMessage

/-- Security List Cancellation Report Message: 50 bytes -/
structure SecurityListCancellationReportMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  deriving DecidableEq, Repr

namespace SecurityListCancellationReportMessage

def encode (message : SecurityListCancellationReportMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin)))))

def decode (bytes : List UInt8) : Option (SecurityListCancellationReportMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin }, bytes)

@[simp] theorem encode_length (message : SecurityListCancellationReportMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityListCancellationReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListCancellationReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityListCancellationReportMessage

/-- Statistics Message: 18 bytes -/
structure StatisticsMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  dataCount : BitVec 8
  dataCode : Alpha 1
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.dataCount
    ++ (Alpha.encode message.dataCode))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (dataCount, bytes) ← decodeUIntLE 1 bytes
  let (dataCode, bytes) ← Alpha.decode 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, dataCount, dataCode }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StatisticsMessage

/-- Security List Message: 976 bytes -/
structure SecurityListMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  fisn : Alpha 35
  issuerLei : Alpha 20
  securityGroup : Alpha 2
  cfiCode : Alpha 6
  securityType : Alpha 2
  maturityDate : BitVec 32
  issueDate : BitVec 32
  contractMultiplier : BitVec 64
  liSpre : BitVec 64
  sstIpre : BitVec 64
  liSpost : BitVec 64
  sstIpost : BitVec 64
  liquidInstrument : BitVec 8
  admissionRequestedByIssuer : BitVec 8
  minTradeVol : BitVec 32
  roundLot : BitVec 32
  currency : Alpha 3
  modalityMaskB4 : BitVec 32
  securityDescription : Alpha 80
  tradingObligation : BitVec 8
  securityName : Alpha 40
  netAssetValueIdentifier : Alpha 7
  securitySubType : Alpha 2
  maturityMonthYear : Alpha 8
  securityStatus : SecurityStatus
  strikePrice : BitVec 64
  strikeValue : BitVec 64
  exerciseStyle : ExerciseStyle
  putOrCall : PutOrCall
  positionLimit : BitVec 64
  ntPositionLimit : BitVec 64
  issuer : Alpha 12
  cpRegType : BitVec 8
  barrier : BitVec 64
  lastTradingDay : BitVec 32
  automaticExpiration : BitVec 8
  feeType : Alpha 2
  barrier2 : BitVec 64
  triggerBarrier : BitVec 64
  triggerUpperBarrier : BitVec 64
  averageQuarterlyTurnover : BitVec 64
  tradingScope : BitVec 8
  sicavCounterpartyMember : Alpha 4
  netAssetValueIndicator : BitVec 8
  referenceTradingVenue : ReferenceTradingVenue
  outstandingCapital : BitVec 64
  firstTradingDate : BitVec 32
  settlementSystem : SettlementSystem
  numberOfDecimals : BitVec 8
  numberOfHolders : BitVec 32
  outstandingShares : BitVec 32
  minimumAuthorizedShares : BitVec 32
  minimumCapital : BitVec 64
  lastAdmissionDate : BitVec 32
  barrierReturn : BitVec 64
  investmentFundManager : Alpha 80
  effectiveAmountFiltersRoutedOrders : BitVec 64
  orderNumberOfDecimals : BitVec 8
  investmentFundClass : BitVec 8
  masterFundName : Alpha 80
  investmentFundManagementCompany : Alpha 80
  investmentFundDepository : Alpha 80
  investmentFundCategory : Alpha 80
  investmentFundMinimumSubscriptionAmount : BitVec 64
  investmentFundMinimumMaintenanceAmount : BitVec 64
  investmentFundCutOffTime : BitVec 64
  navCommunicationTerm : NavCommunicationTerm
  investmentFundNumberOfDecimals : BitVec 8
  commodityDerivativeIndicator : CommodityDerivativeIndicator
  doubleVolumeCapReached : BitVec 8
  adt : BitVec 64
  baseProduct : Alpha 4
  subProduct : Alpha 4
  furtherSubProduct : Alpha 4
  adnt : BitVec 64
  priceTickRule : BitVec 8
  underlyingSymbol : Alpha 22
  underlyingIsin : Alpha 12
  underlyingCurrency : Alpha 3
  minimumDisplayQty : BitVec 32
  retailServiceFlag : BitVec 8
  selfMatchPrevention : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityListMessage

def encode (message : SecurityListMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin
    ++ (Alpha.encode message.fisn
    ++ (Alpha.encode message.issuerLei
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.securityType
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (encodeUIntLE 4 message.issueDate
    ++ (encodeUIntLE 8 message.contractMultiplier
    ++ (encodeUIntLE 8 message.liSpre
    ++ (encodeUIntLE 8 message.sstIpre
    ++ (encodeUIntLE 8 message.liSpost
    ++ (encodeUIntLE 8 message.sstIpost
    ++ (encodeUIntLE 1 message.liquidInstrument
    ++ (encodeUIntLE 1 message.admissionRequestedByIssuer
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.roundLot
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 4 message.modalityMaskB4
    ++ (Alpha.encode message.securityDescription
    ++ (encodeUIntLE 1 message.tradingObligation
    ++ (Alpha.encode message.securityName
    ++ (Alpha.encode message.netAssetValueIdentifier
    ++ (Alpha.encode message.securitySubType
    ++ (Alpha.encode message.maturityMonthYear
    ++ (SecurityStatus.encode message.securityStatus
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.strikeValue
    ++ (ExerciseStyle.encode message.exerciseStyle
    ++ (PutOrCall.encode message.putOrCall
    ++ (encodeUIntLE 8 message.positionLimit
    ++ (encodeUIntLE 8 message.ntPositionLimit
    ++ (Alpha.encode message.issuer
    ++ (encodeUIntLE 1 message.cpRegType
    ++ (encodeUIntLE 8 message.barrier
    ++ (encodeUIntLE 4 message.lastTradingDay
    ++ (encodeUIntLE 1 message.automaticExpiration
    ++ (Alpha.encode message.feeType
    ++ (encodeUIntLE 8 message.barrier2
    ++ (encodeUIntLE 8 message.triggerBarrier
    ++ (encodeUIntLE 8 message.triggerUpperBarrier
    ++ (encodeUIntLE 8 message.averageQuarterlyTurnover
    ++ (encodeUIntLE 1 message.tradingScope
    ++ (Alpha.encode message.sicavCounterpartyMember
    ++ (encodeUIntLE 1 message.netAssetValueIndicator
    ++ (ReferenceTradingVenue.encode message.referenceTradingVenue
    ++ (encodeUIntLE 8 message.outstandingCapital
    ++ (encodeUIntLE 4 message.firstTradingDate
    ++ (SettlementSystem.encode message.settlementSystem
    ++ (encodeUIntLE 1 message.numberOfDecimals
    ++ (encodeUIntLE 4 message.numberOfHolders
    ++ (encodeUIntLE 4 message.outstandingShares
    ++ (encodeUIntLE 4 message.minimumAuthorizedShares
    ++ (encodeUIntLE 8 message.minimumCapital
    ++ (encodeUIntLE 4 message.lastAdmissionDate
    ++ (encodeUIntLE 8 message.barrierReturn
    ++ (Alpha.encode message.investmentFundManager
    ++ (encodeUIntLE 8 message.effectiveAmountFiltersRoutedOrders
    ++ (encodeUIntLE 1 message.orderNumberOfDecimals
    ++ (encodeUIntLE 1 message.investmentFundClass
    ++ (Alpha.encode message.masterFundName
    ++ (Alpha.encode message.investmentFundManagementCompany
    ++ (Alpha.encode message.investmentFundDepository
    ++ (Alpha.encode message.investmentFundCategory
    ++ (encodeUIntLE 8 message.investmentFundMinimumSubscriptionAmount
    ++ (encodeUIntLE 8 message.investmentFundMinimumMaintenanceAmount
    ++ (encodeUIntLE 8 message.investmentFundCutOffTime
    ++ (NavCommunicationTerm.encode message.navCommunicationTerm
    ++ (encodeUIntLE 1 message.investmentFundNumberOfDecimals
    ++ (CommodityDerivativeIndicator.encode message.commodityDerivativeIndicator
    ++ (encodeUIntLE 1 message.doubleVolumeCapReached
    ++ (encodeUIntLE 8 message.adt
    ++ (Alpha.encode message.baseProduct
    ++ (Alpha.encode message.subProduct
    ++ (Alpha.encode message.furtherSubProduct
    ++ (encodeUIntLE 8 message.adnt
    ++ (encodeUIntLE 1 message.priceTickRule
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.underlyingIsin
    ++ (Alpha.encode message.underlyingCurrency
    ++ (encodeUIntLE 4 message.minimumDisplayQty
    ++ (encodeUIntLE 1 message.retailServiceFlag
    ++ (encodeUIntLE 1 message.selfMatchPrevention)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityListMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  let (fisn, bytes) ← Alpha.decode 35 bytes
  let (issuerLei, bytes) ← Alpha.decode 20 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (securityType, bytes) ← Alpha.decode 2 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (issueDate, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (liSpre, bytes) ← decodeUIntLE 8 bytes
  let (sstIpre, bytes) ← decodeUIntLE 8 bytes
  let (liSpost, bytes) ← decodeUIntLE 8 bytes
  let (sstIpost, bytes) ← decodeUIntLE 8 bytes
  let (liquidInstrument, bytes) ← decodeUIntLE 1 bytes
  let (admissionRequestedByIssuer, bytes) ← decodeUIntLE 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (roundLot, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (modalityMaskB4, bytes) ← decodeUIntLE 4 bytes
  let (securityDescription, bytes) ← Alpha.decode 80 bytes
  let (tradingObligation, bytes) ← decodeUIntLE 1 bytes
  let (securityName, bytes) ← Alpha.decode 40 bytes
  let (netAssetValueIdentifier, bytes) ← Alpha.decode 7 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (maturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikeValue, bytes) ← decodeUIntLE 8 bytes
  let (exerciseStyle, bytes) ← ExerciseStyle.decode bytes
  let (putOrCall, bytes) ← PutOrCall.decode bytes
  let (positionLimit, bytes) ← decodeUIntLE 8 bytes
  let (ntPositionLimit, bytes) ← decodeUIntLE 8 bytes
  let (issuer, bytes) ← Alpha.decode 12 bytes
  let (cpRegType, bytes) ← decodeUIntLE 1 bytes
  let (barrier, bytes) ← decodeUIntLE 8 bytes
  let (lastTradingDay, bytes) ← decodeUIntLE 4 bytes
  let (automaticExpiration, bytes) ← decodeUIntLE 1 bytes
  let (feeType, bytes) ← Alpha.decode 2 bytes
  let (barrier2, bytes) ← decodeUIntLE 8 bytes
  let (triggerBarrier, bytes) ← decodeUIntLE 8 bytes
  let (triggerUpperBarrier, bytes) ← decodeUIntLE 8 bytes
  let (averageQuarterlyTurnover, bytes) ← decodeUIntLE 8 bytes
  let (tradingScope, bytes) ← decodeUIntLE 1 bytes
  let (sicavCounterpartyMember, bytes) ← Alpha.decode 4 bytes
  let (netAssetValueIndicator, bytes) ← decodeUIntLE 1 bytes
  let (referenceTradingVenue, bytes) ← ReferenceTradingVenue.decode bytes
  let (outstandingCapital, bytes) ← decodeUIntLE 8 bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (settlementSystem, bytes) ← SettlementSystem.decode bytes
  let (numberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (numberOfHolders, bytes) ← decodeUIntLE 4 bytes
  let (outstandingShares, bytes) ← decodeUIntLE 4 bytes
  let (minimumAuthorizedShares, bytes) ← decodeUIntLE 4 bytes
  let (minimumCapital, bytes) ← decodeUIntLE 8 bytes
  let (lastAdmissionDate, bytes) ← decodeUIntLE 4 bytes
  let (barrierReturn, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundManager, bytes) ← Alpha.decode 80 bytes
  let (effectiveAmountFiltersRoutedOrders, bytes) ← decodeUIntLE 8 bytes
  let (orderNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (investmentFundClass, bytes) ← decodeUIntLE 1 bytes
  let (masterFundName, bytes) ← Alpha.decode 80 bytes
  let (investmentFundManagementCompany, bytes) ← Alpha.decode 80 bytes
  let (investmentFundDepository, bytes) ← Alpha.decode 80 bytes
  let (investmentFundCategory, bytes) ← Alpha.decode 80 bytes
  let (investmentFundMinimumSubscriptionAmount, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundMinimumMaintenanceAmount, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundCutOffTime, bytes) ← decodeUIntLE 8 bytes
  let (navCommunicationTerm, bytes) ← NavCommunicationTerm.decode bytes
  let (investmentFundNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (commodityDerivativeIndicator, bytes) ← CommodityDerivativeIndicator.decode bytes
  let (doubleVolumeCapReached, bytes) ← decodeUIntLE 1 bytes
  let (adt, bytes) ← decodeUIntLE 8 bytes
  let (baseProduct, bytes) ← Alpha.decode 4 bytes
  let (subProduct, bytes) ← Alpha.decode 4 bytes
  let (furtherSubProduct, bytes) ← Alpha.decode 4 bytes
  let (adnt, bytes) ← decodeUIntLE 8 bytes
  let (priceTickRule, bytes) ← decodeUIntLE 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 22 bytes
  let (underlyingIsin, bytes) ← Alpha.decode 12 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (minimumDisplayQty, bytes) ← decodeUIntLE 4 bytes
  let (retailServiceFlag, bytes) ← decodeUIntLE 1 bytes
  let (selfMatchPrevention, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin, fisn, issuerLei, securityGroup, cfiCode, securityType, maturityDate, issueDate, contractMultiplier, liSpre, sstIpre, liSpost, sstIpost, liquidInstrument, admissionRequestedByIssuer, minTradeVol, roundLot, currency, modalityMaskB4, securityDescription, tradingObligation, securityName, netAssetValueIdentifier, securitySubType, maturityMonthYear, securityStatus, strikePrice, strikeValue, exerciseStyle, putOrCall, positionLimit, ntPositionLimit, issuer, cpRegType, barrier, lastTradingDay, automaticExpiration, feeType, barrier2, triggerBarrier, triggerUpperBarrier, averageQuarterlyTurnover, tradingScope, sicavCounterpartyMember, netAssetValueIndicator, referenceTradingVenue, outstandingCapital, firstTradingDate, settlementSystem, numberOfDecimals, numberOfHolders, outstandingShares, minimumAuthorizedShares, minimumCapital, lastAdmissionDate, barrierReturn, investmentFundManager, effectiveAmountFiltersRoutedOrders, orderNumberOfDecimals, investmentFundClass, masterFundName, investmentFundManagementCompany, investmentFundDepository, investmentFundCategory, investmentFundMinimumSubscriptionAmount, investmentFundMinimumMaintenanceAmount, investmentFundCutOffTime, navCommunicationTerm, investmentFundNumberOfDecimals, commodityDerivativeIndicator, doubleVolumeCapReached, adt, baseProduct, subProduct, furtherSubProduct, adnt, priceTickRule, underlyingSymbol, underlyingIsin, underlyingCurrency, minimumDisplayQty, retailServiceFlag, selfMatchPrevention }, bytes)

@[simp] theorem encode_length (message : SecurityListMessage) : (encode message).length = 976 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SecurityStatus.encode_length, ExerciseStyle.encode_length, PutOrCall.encode_length, ReferenceTradingVenue.encode_length, SettlementSystem.encode_length, NavCommunicationTerm.encode_length, CommodityDerivativeIndicator.encode_length]

theorem encode_length_pos (message : SecurityListMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityListMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseStyle.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PutOrCall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ReferenceTradingVenue.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementSystem.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, NavCommunicationTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CommodityDerivativeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListMessage

/-- Security List Update Report Message: 976 bytes -/
structure SecurityListUpdateReportMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  fisn : Alpha 35
  issuerLei : Alpha 20
  securityGroup : Alpha 2
  cfiCode : Alpha 6
  securityType : Alpha 2
  maturityDate : BitVec 32
  issueDate : BitVec 32
  contractMultiplier : BitVec 64
  liSpre : BitVec 64
  sstIpre : BitVec 64
  liSpost : BitVec 64
  sstIpost : BitVec 64
  liquidInstrument : BitVec 8
  admissionRequestedByIssuer : BitVec 8
  minTradeVol : BitVec 32
  roundLot : BitVec 32
  currency : Alpha 3
  modalityMaskB4 : BitVec 32
  securityDescription : Alpha 80
  tradingObligation : BitVec 8
  securityName : Alpha 40
  netAssetValueIdentifier : Alpha 7
  securitySubType : Alpha 2
  maturityMonthYear : Alpha 8
  securityStatus : SecurityStatus
  strikePrice : BitVec 64
  strikeValue : BitVec 64
  exerciseStyle : ExerciseStyle
  putOrCall : PutOrCall
  positionLimit : BitVec 64
  ntPositionLimit : BitVec 64
  issuer : Alpha 12
  cpRegType : BitVec 8
  barrier : BitVec 64
  lastTradingDay : BitVec 32
  automaticExpiration : BitVec 8
  feeType : Alpha 2
  barrier2 : BitVec 64
  triggerBarrier : BitVec 64
  triggerUpperBarrier : BitVec 64
  averageQuarterlyTurnover : BitVec 64
  tradingScope : BitVec 8
  sicavCounterpartyMember : Alpha 4
  netAssetValueIndicator : BitVec 8
  referenceTradingVenue : ReferenceTradingVenue
  outstandingCapital : BitVec 64
  firstTradingDate : BitVec 32
  settlementSystem : SettlementSystem
  numberOfDecimals : BitVec 8
  numberOfHolders : BitVec 32
  outstandingShares : BitVec 32
  minimumAuthorizedShares : BitVec 32
  minimumCapital : BitVec 64
  lastAdmissionDate : BitVec 32
  barrierReturn : BitVec 64
  investmentFundManager : Alpha 80
  effectiveAmountFiltersRoutedOrders : BitVec 64
  orderNumberOfDecimals : BitVec 8
  investmentFundClass : BitVec 8
  masterFundName : Alpha 80
  investmentFundManagementCompany : Alpha 80
  investmentFundDepository : Alpha 80
  investmentFundCategory : Alpha 80
  investmentFundMinimumSubscriptionAmount : BitVec 64
  investmentFundMinimumMaintenanceAmount : BitVec 64
  investmentFundCutOffTime : BitVec 64
  navCommunicationTerm : NavCommunicationTerm
  investmentFundNumberOfDecimals : BitVec 8
  commodityDerivativeIndicator : CommodityDerivativeIndicator
  doubleVolumeCapReached : BitVec 8
  adt : BitVec 64
  baseProduct : Alpha 4
  subProduct : Alpha 4
  furtherSubProduct : Alpha 4
  adnt : BitVec 64
  priceTickRule : BitVec 8
  underlyingSymbol : Alpha 22
  underlyingIsin : Alpha 12
  underlyingCurrency : Alpha 3
  minimumDisplayQty : BitVec 32
  retailServiceFlag : BitVec 8
  selfMatchPrevention : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityListUpdateReportMessage

def encode (message : SecurityListUpdateReportMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin
    ++ (Alpha.encode message.fisn
    ++ (Alpha.encode message.issuerLei
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.securityType
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (encodeUIntLE 4 message.issueDate
    ++ (encodeUIntLE 8 message.contractMultiplier
    ++ (encodeUIntLE 8 message.liSpre
    ++ (encodeUIntLE 8 message.sstIpre
    ++ (encodeUIntLE 8 message.liSpost
    ++ (encodeUIntLE 8 message.sstIpost
    ++ (encodeUIntLE 1 message.liquidInstrument
    ++ (encodeUIntLE 1 message.admissionRequestedByIssuer
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.roundLot
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 4 message.modalityMaskB4
    ++ (Alpha.encode message.securityDescription
    ++ (encodeUIntLE 1 message.tradingObligation
    ++ (Alpha.encode message.securityName
    ++ (Alpha.encode message.netAssetValueIdentifier
    ++ (Alpha.encode message.securitySubType
    ++ (Alpha.encode message.maturityMonthYear
    ++ (SecurityStatus.encode message.securityStatus
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.strikeValue
    ++ (ExerciseStyle.encode message.exerciseStyle
    ++ (PutOrCall.encode message.putOrCall
    ++ (encodeUIntLE 8 message.positionLimit
    ++ (encodeUIntLE 8 message.ntPositionLimit
    ++ (Alpha.encode message.issuer
    ++ (encodeUIntLE 1 message.cpRegType
    ++ (encodeUIntLE 8 message.barrier
    ++ (encodeUIntLE 4 message.lastTradingDay
    ++ (encodeUIntLE 1 message.automaticExpiration
    ++ (Alpha.encode message.feeType
    ++ (encodeUIntLE 8 message.barrier2
    ++ (encodeUIntLE 8 message.triggerBarrier
    ++ (encodeUIntLE 8 message.triggerUpperBarrier
    ++ (encodeUIntLE 8 message.averageQuarterlyTurnover
    ++ (encodeUIntLE 1 message.tradingScope
    ++ (Alpha.encode message.sicavCounterpartyMember
    ++ (encodeUIntLE 1 message.netAssetValueIndicator
    ++ (ReferenceTradingVenue.encode message.referenceTradingVenue
    ++ (encodeUIntLE 8 message.outstandingCapital
    ++ (encodeUIntLE 4 message.firstTradingDate
    ++ (SettlementSystem.encode message.settlementSystem
    ++ (encodeUIntLE 1 message.numberOfDecimals
    ++ (encodeUIntLE 4 message.numberOfHolders
    ++ (encodeUIntLE 4 message.outstandingShares
    ++ (encodeUIntLE 4 message.minimumAuthorizedShares
    ++ (encodeUIntLE 8 message.minimumCapital
    ++ (encodeUIntLE 4 message.lastAdmissionDate
    ++ (encodeUIntLE 8 message.barrierReturn
    ++ (Alpha.encode message.investmentFundManager
    ++ (encodeUIntLE 8 message.effectiveAmountFiltersRoutedOrders
    ++ (encodeUIntLE 1 message.orderNumberOfDecimals
    ++ (encodeUIntLE 1 message.investmentFundClass
    ++ (Alpha.encode message.masterFundName
    ++ (Alpha.encode message.investmentFundManagementCompany
    ++ (Alpha.encode message.investmentFundDepository
    ++ (Alpha.encode message.investmentFundCategory
    ++ (encodeUIntLE 8 message.investmentFundMinimumSubscriptionAmount
    ++ (encodeUIntLE 8 message.investmentFundMinimumMaintenanceAmount
    ++ (encodeUIntLE 8 message.investmentFundCutOffTime
    ++ (NavCommunicationTerm.encode message.navCommunicationTerm
    ++ (encodeUIntLE 1 message.investmentFundNumberOfDecimals
    ++ (CommodityDerivativeIndicator.encode message.commodityDerivativeIndicator
    ++ (encodeUIntLE 1 message.doubleVolumeCapReached
    ++ (encodeUIntLE 8 message.adt
    ++ (Alpha.encode message.baseProduct
    ++ (Alpha.encode message.subProduct
    ++ (Alpha.encode message.furtherSubProduct
    ++ (encodeUIntLE 8 message.adnt
    ++ (encodeUIntLE 1 message.priceTickRule
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.underlyingIsin
    ++ (Alpha.encode message.underlyingCurrency
    ++ (encodeUIntLE 4 message.minimumDisplayQty
    ++ (encodeUIntLE 1 message.retailServiceFlag
    ++ (encodeUIntLE 1 message.selfMatchPrevention)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityListUpdateReportMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  let (fisn, bytes) ← Alpha.decode 35 bytes
  let (issuerLei, bytes) ← Alpha.decode 20 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (securityType, bytes) ← Alpha.decode 2 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (issueDate, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (liSpre, bytes) ← decodeUIntLE 8 bytes
  let (sstIpre, bytes) ← decodeUIntLE 8 bytes
  let (liSpost, bytes) ← decodeUIntLE 8 bytes
  let (sstIpost, bytes) ← decodeUIntLE 8 bytes
  let (liquidInstrument, bytes) ← decodeUIntLE 1 bytes
  let (admissionRequestedByIssuer, bytes) ← decodeUIntLE 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (roundLot, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (modalityMaskB4, bytes) ← decodeUIntLE 4 bytes
  let (securityDescription, bytes) ← Alpha.decode 80 bytes
  let (tradingObligation, bytes) ← decodeUIntLE 1 bytes
  let (securityName, bytes) ← Alpha.decode 40 bytes
  let (netAssetValueIdentifier, bytes) ← Alpha.decode 7 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (maturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikeValue, bytes) ← decodeUIntLE 8 bytes
  let (exerciseStyle, bytes) ← ExerciseStyle.decode bytes
  let (putOrCall, bytes) ← PutOrCall.decode bytes
  let (positionLimit, bytes) ← decodeUIntLE 8 bytes
  let (ntPositionLimit, bytes) ← decodeUIntLE 8 bytes
  let (issuer, bytes) ← Alpha.decode 12 bytes
  let (cpRegType, bytes) ← decodeUIntLE 1 bytes
  let (barrier, bytes) ← decodeUIntLE 8 bytes
  let (lastTradingDay, bytes) ← decodeUIntLE 4 bytes
  let (automaticExpiration, bytes) ← decodeUIntLE 1 bytes
  let (feeType, bytes) ← Alpha.decode 2 bytes
  let (barrier2, bytes) ← decodeUIntLE 8 bytes
  let (triggerBarrier, bytes) ← decodeUIntLE 8 bytes
  let (triggerUpperBarrier, bytes) ← decodeUIntLE 8 bytes
  let (averageQuarterlyTurnover, bytes) ← decodeUIntLE 8 bytes
  let (tradingScope, bytes) ← decodeUIntLE 1 bytes
  let (sicavCounterpartyMember, bytes) ← Alpha.decode 4 bytes
  let (netAssetValueIndicator, bytes) ← decodeUIntLE 1 bytes
  let (referenceTradingVenue, bytes) ← ReferenceTradingVenue.decode bytes
  let (outstandingCapital, bytes) ← decodeUIntLE 8 bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (settlementSystem, bytes) ← SettlementSystem.decode bytes
  let (numberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (numberOfHolders, bytes) ← decodeUIntLE 4 bytes
  let (outstandingShares, bytes) ← decodeUIntLE 4 bytes
  let (minimumAuthorizedShares, bytes) ← decodeUIntLE 4 bytes
  let (minimumCapital, bytes) ← decodeUIntLE 8 bytes
  let (lastAdmissionDate, bytes) ← decodeUIntLE 4 bytes
  let (barrierReturn, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundManager, bytes) ← Alpha.decode 80 bytes
  let (effectiveAmountFiltersRoutedOrders, bytes) ← decodeUIntLE 8 bytes
  let (orderNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (investmentFundClass, bytes) ← decodeUIntLE 1 bytes
  let (masterFundName, bytes) ← Alpha.decode 80 bytes
  let (investmentFundManagementCompany, bytes) ← Alpha.decode 80 bytes
  let (investmentFundDepository, bytes) ← Alpha.decode 80 bytes
  let (investmentFundCategory, bytes) ← Alpha.decode 80 bytes
  let (investmentFundMinimumSubscriptionAmount, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundMinimumMaintenanceAmount, bytes) ← decodeUIntLE 8 bytes
  let (investmentFundCutOffTime, bytes) ← decodeUIntLE 8 bytes
  let (navCommunicationTerm, bytes) ← NavCommunicationTerm.decode bytes
  let (investmentFundNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (commodityDerivativeIndicator, bytes) ← CommodityDerivativeIndicator.decode bytes
  let (doubleVolumeCapReached, bytes) ← decodeUIntLE 1 bytes
  let (adt, bytes) ← decodeUIntLE 8 bytes
  let (baseProduct, bytes) ← Alpha.decode 4 bytes
  let (subProduct, bytes) ← Alpha.decode 4 bytes
  let (furtherSubProduct, bytes) ← Alpha.decode 4 bytes
  let (adnt, bytes) ← decodeUIntLE 8 bytes
  let (priceTickRule, bytes) ← decodeUIntLE 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 22 bytes
  let (underlyingIsin, bytes) ← Alpha.decode 12 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (minimumDisplayQty, bytes) ← decodeUIntLE 4 bytes
  let (retailServiceFlag, bytes) ← decodeUIntLE 1 bytes
  let (selfMatchPrevention, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin, fisn, issuerLei, securityGroup, cfiCode, securityType, maturityDate, issueDate, contractMultiplier, liSpre, sstIpre, liSpost, sstIpost, liquidInstrument, admissionRequestedByIssuer, minTradeVol, roundLot, currency, modalityMaskB4, securityDescription, tradingObligation, securityName, netAssetValueIdentifier, securitySubType, maturityMonthYear, securityStatus, strikePrice, strikeValue, exerciseStyle, putOrCall, positionLimit, ntPositionLimit, issuer, cpRegType, barrier, lastTradingDay, automaticExpiration, feeType, barrier2, triggerBarrier, triggerUpperBarrier, averageQuarterlyTurnover, tradingScope, sicavCounterpartyMember, netAssetValueIndicator, referenceTradingVenue, outstandingCapital, firstTradingDate, settlementSystem, numberOfDecimals, numberOfHolders, outstandingShares, minimumAuthorizedShares, minimumCapital, lastAdmissionDate, barrierReturn, investmentFundManager, effectiveAmountFiltersRoutedOrders, orderNumberOfDecimals, investmentFundClass, masterFundName, investmentFundManagementCompany, investmentFundDepository, investmentFundCategory, investmentFundMinimumSubscriptionAmount, investmentFundMinimumMaintenanceAmount, investmentFundCutOffTime, navCommunicationTerm, investmentFundNumberOfDecimals, commodityDerivativeIndicator, doubleVolumeCapReached, adt, baseProduct, subProduct, furtherSubProduct, adnt, priceTickRule, underlyingSymbol, underlyingIsin, underlyingCurrency, minimumDisplayQty, retailServiceFlag, selfMatchPrevention }, bytes)

@[simp] theorem encode_length (message : SecurityListUpdateReportMessage) : (encode message).length = 976 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SecurityStatus.encode_length, ExerciseStyle.encode_length, PutOrCall.encode_length, ReferenceTradingVenue.encode_length, SettlementSystem.encode_length, NavCommunicationTerm.encode_length, CommodityDerivativeIndicator.encode_length]

theorem encode_length_pos (message : SecurityListUpdateReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityListUpdateReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseStyle.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PutOrCall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ReferenceTradingVenue.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementSystem.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, NavCommunicationTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CommodityDerivativeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListUpdateReportMessage

/-- Security Status Message: 115 bytes -/
structure SecurityStatusMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  referencePrice : BitVec 64
  staticPrice : BitVec 64
  dynamicPriceOscilationPercentage : BitVec 64
  dynamicRangeMultiplier : BitVec 8
  auctionTriggerPrice : BitVec 64
  auctionEndTime : BitVec 64
  liquidativeValueDate : BitVec 32
  bonusWarrantsWithActiveBonus : BitVec 8
  securityTradingStatus : BitVec 8
  auctionOrigin : BitVec 8
  nonAvailabilityReason : BitVec 8
  exemptionSituation : ExemptionSituation
  blockOscilationPercentage : BitVec 64
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  liquidativeValue : BitVec 64
  staticRangeType : StaticRangeType
  orderStaticRange : BitVec 64
  blockStaticRange : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 8 message.referencePrice
    ++ (encodeUIntLE 8 message.staticPrice
    ++ (encodeUIntLE 8 message.dynamicPriceOscilationPercentage
    ++ (encodeUIntLE 1 message.dynamicRangeMultiplier
    ++ (encodeUIntLE 8 message.auctionTriggerPrice
    ++ (encodeUIntLE 8 message.auctionEndTime
    ++ (encodeUIntLE 4 message.liquidativeValueDate
    ++ (encodeUIntLE 1 message.bonusWarrantsWithActiveBonus
    ++ (encodeUIntLE 1 message.securityTradingStatus
    ++ (encodeUIntLE 1 message.auctionOrigin
    ++ (encodeUIntLE 1 message.nonAvailabilityReason
    ++ (ExemptionSituation.encode message.exemptionSituation
    ++ (encodeUIntLE 8 message.blockOscilationPercentage
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.liquidativeValue
    ++ (StaticRangeType.encode message.staticRangeType
    ++ (encodeUIntLE 8 message.orderStaticRange
    ++ (encodeUIntLE 8 message.blockStaticRange)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (referencePrice, bytes) ← decodeUIntLE 8 bytes
  let (staticPrice, bytes) ← decodeUIntLE 8 bytes
  let (dynamicPriceOscilationPercentage, bytes) ← decodeUIntLE 8 bytes
  let (dynamicRangeMultiplier, bytes) ← decodeUIntLE 1 bytes
  let (auctionTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (auctionEndTime, bytes) ← decodeUIntLE 8 bytes
  let (liquidativeValueDate, bytes) ← decodeUIntLE 4 bytes
  let (bonusWarrantsWithActiveBonus, bytes) ← decodeUIntLE 1 bytes
  let (securityTradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (auctionOrigin, bytes) ← decodeUIntLE 1 bytes
  let (nonAvailabilityReason, bytes) ← decodeUIntLE 1 bytes
  let (exemptionSituation, bytes) ← ExemptionSituation.decode bytes
  let (blockOscilationPercentage, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (liquidativeValue, bytes) ← decodeUIntLE 8 bytes
  let (staticRangeType, bytes) ← StaticRangeType.decode bytes
  let (orderStaticRange, bytes) ← decodeUIntLE 8 bytes
  let (blockStaticRange, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, referencePrice, staticPrice, dynamicPriceOscilationPercentage, dynamicRangeMultiplier, auctionTriggerPrice, auctionEndTime, liquidativeValueDate, bonusWarrantsWithActiveBonus, securityTradingStatus, auctionOrigin, nonAvailabilityReason, exemptionSituation, blockOscilationPercentage, highLimitPrice, lowLimitPrice, liquidativeValue, staticRangeType, orderStaticRange, blockStaticRange }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ExemptionSituation.encode_length, StaticRangeType.encode_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExemptionSituation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, StaticRangeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusMessage

/-- Order Book Clear Message: 16 bytes -/
structure OrderBookClearMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderBookClearMessage

def encode (message : OrderBookClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime))

def decode (bytes : List UInt8) : Option (OrderBookClearMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime }, bytes)

@[simp] theorem encode_length (message : OrderBookClearMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderBookClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookClearMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderBookClearMessage

/-- Order Market Pre Transparency Information Message: 42 bytes -/
structure OrderMarketPreTransparencyInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  retailFlag : BitVec 8
  side : Side
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  deriving DecidableEq, Repr

namespace OrderMarketPreTransparencyInformationMessage

def encode (message : OrderMarketPreTransparencyInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 1 message.retailFlag
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty)))))))))

def decode (bytes : List UInt8) : Option (OrderMarketPreTransparencyInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, entryDate, retailFlag, side, priority, price, displayQty }, bytes)

@[simp] theorem encode_length (message : OrderMarketPreTransparencyInformationMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : OrderMarketPreTransparencyInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMarketPreTransparencyInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderMarketPreTransparencyInformationMessage

/-- Quote Market Pre Transparency Information Message: 57 bytes -/
structure QuoteMarketPreTransparencyInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  secondaryOrderId2 : BitVec 32
  retailFlag : BitVec 8
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteMarketPreTransparencyInformationMessage

def encode (message : QuoteMarketPreTransparencyInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 1 message.retailFlag
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2)))))))))))

def decode (bytes : List UInt8) : Option (QuoteMarketPreTransparencyInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, secondaryOrderId2, retailFlag, priority, price, displayQty, priority2, price2, displayQty2 }, bytes)

@[simp] theorem encode_length (message : QuoteMarketPreTransparencyInformationMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteMarketPreTransparencyInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMarketPreTransparencyInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteMarketPreTransparencyInformationMessage

/-- Order Cancellation Market Member Message: 25 bytes -/
structure OrderCancellationMarketMemberMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  retailFlag : BitVec 8
  deriving DecidableEq, Repr

namespace OrderCancellationMarketMemberMessage

def encode (message : OrderCancellationMarketMemberMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 1 message.retailFlag)))))

def decode (bytes : List UInt8) : Option (OrderCancellationMarketMemberMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, entryDate, retailFlag }, bytes)

@[simp] theorem encode_length (message : OrderCancellationMarketMemberMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancellationMarketMemberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationMarketMemberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancellationMarketMemberMessage

/-- Quote Cancellation Market Member Message: 25 bytes -/
structure QuoteCancellationMarketMemberMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  secondaryOrderId2 : BitVec 32
  retailFlag : BitVec 8
  deriving DecidableEq, Repr

namespace QuoteCancellationMarketMemberMessage

def encode (message : QuoteCancellationMarketMemberMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 1 message.retailFlag)))))

def decode (bytes : List UInt8) : Option (QuoteCancellationMarketMemberMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, secondaryOrderId2, retailFlag }, bytes)

@[simp] theorem encode_length (message : QuoteCancellationMarketMemberMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancellationMarketMemberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancellationMarketMemberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteCancellationMarketMemberMessage

/-- Trade Market Post Transparency Information Topofbook Message: 55 bytes -/
structure TradeMarketPostTransparencyInformationTopofbookMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  deriving DecidableEq, Repr

namespace TradeMarketPostTransparencyInformationTopofbookMessage

def encode (message : TradeMarketPostTransparencyInformationTopofbookMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory)))))))))))))))

def decode (bytes : List UInt8) : Option (TradeMarketPostTransparencyInformationTopofbookMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory }, bytes)

@[simp] theorem encode_length (message : TradeMarketPostTransparencyInformationTopofbookMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length]

theorem encode_length_pos (message : TradeMarketPostTransparencyInformationTopofbookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMarketPostTransparencyInformationTopofbookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TransactionCategory.decode_encode, some_bind]
  rfl

end TradeMarketPostTransparencyInformationTopofbookMessage

/-- Trade Trade Amendment Or Cancellation Message: 98 bytes -/
structure TradeTradeAmendmentOrCancellationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  lastChangeFlagF1 : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  volumeFloat : BitVec 64
  sicavFundCounterpartySide : SicavFundCounterpartySide
  amendedTradeType : AmendedTradeType
  execRefId : BitVec 32
  amendedTradeDate : BitVec 32
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellationMessage

def encode (message : TradeTradeAmendmentOrCancellationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 1 message.lastChangeFlagF1
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (encodeUIntLE 8 message.volumeFloat
    ++ (SicavFundCounterpartySide.encode message.sicavFundCounterpartySide
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (lastChangeFlagF1, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (volumeFloat, bytes) ← decodeUIntLE 8 bytes
  let (sicavFundCounterpartySide, bytes) ← SicavFundCounterpartySide.decode bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, lastChangeFlagF1, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, publishDateAndTime, tradeDate, tradeSessionDate, volumeFloat, sicavFundCounterpartySide, amendedTradeType, execRefId, amendedTradeDate }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellationMessage) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, SicavFundCounterpartySide.encode_length, AmendedTradeType.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BencrfptFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreTradeTransparencyWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SicavFundCounterpartySide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeTradeAmendmentOrCancellationMessage

/-- Trade Market Post Transparency Information Full Depth Message: 105 bytes -/
structure TradeMarketPostTransparencyInformationFullDepthMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  retailFlag : BitVec 8
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  retailFlag2 : BitVec 8
  deriving DecidableEq, Repr

namespace TradeMarketPostTransparencyInformationFullDepthMessage

def encode (message : TradeMarketPostTransparencyInformationFullDepthMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 1 message.retailFlag
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 1 message.retailFlag2)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeMarketPostTransparencyInformationFullDepthMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag2, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, secondaryOrderId, entryDate, priority, price, displayQty, retailFlag, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, retailFlag2 }, bytes)

@[simp] theorem encode_length (message : TradeMarketPostTransparencyInformationFullDepthMessage) : (encode message).length = 105 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length]

theorem encode_length_pos (message : TradeMarketPostTransparencyInformationFullDepthMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeMarketPostTransparencyInformationFullDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMarketPostTransparencyInformationFullDepthMessage

/-- Topofbook Message: 44 bytes -/
structure TopofbookMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  bidOrders1 : BitVec 16
  bidSize1 : BitVec 32
  bidPx1 : BitVec 64
  askOrders1 : BitVec 16
  askSize1 : BitVec 32
  askPx1 : BitVec 64
  deriving DecidableEq, Repr

namespace TopofbookMessage

def encode (message : TopofbookMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 2 message.bidOrders1
    ++ (encodeUIntLE 4 message.bidSize1
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 2 message.askOrders1
    ++ (encodeUIntLE 4 message.askSize1
    ++ (encodeUIntLE 8 message.askPx1))))))))

def decode (bytes : List UInt8) : Option (TopofbookMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders1, bytes) ← decodeUIntLE 2 bytes
  let (bidSize1, bytes) ← decodeUIntLE 4 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askOrders1, bytes) ← decodeUIntLE 2 bytes
  let (askSize1, bytes) ← decodeUIntLE 4 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, bidOrders1, bidSize1, bidPx1, askOrders1, askSize1, askPx1 }, bytes)

@[simp] theorem encode_length (message : TopofbookMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TopofbookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopofbookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TopofbookMessage

/-- Order And Quote Client Data Message: 97 bytes -/
structure OrderAndQuoteClientDataMessage where
  requestId : BitVec 32
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  accountBolsa : Alpha 16
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  automaticOrderFilterFlag : AutomaticOrderFilterFlag
  receivedDeptId : ReceivedDeptId
  persistence : Persistence
  accountType : AccountType
  selfMatchPreventionType : SelfMatchPreventionType
  clientDataReference : Alpha 15
  deriving DecidableEq, Repr

namespace OrderAndQuoteClientDataMessage

def encode (message : OrderAndQuoteClientDataMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.accountBolsa
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (AutomaticOrderFilterFlag.encode message.automaticOrderFilterFlag
    ++ (ReceivedDeptId.encode message.receivedDeptId
    ++ (Persistence.encode message.persistence
    ++ (AccountType.encode message.accountType
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.clientDataReference))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAndQuoteClientDataMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (accountBolsa, bytes) ← Alpha.decode 16 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (automaticOrderFilterFlag, bytes) ← AutomaticOrderFilterFlag.decode bytes
  let (receivedDeptId, bytes) ← ReceivedDeptId.decode bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (clientDataReference, bytes) ← Alpha.decode 15 bytes
  pure ({ requestId, clientDataId, algorithmicTradeIndicator, clientId, accountBolsa, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, automaticOrderFilterFlag, receivedDeptId, persistence, accountType, selfMatchPreventionType, clientDataReference }, bytes)

@[simp] theorem encode_length (message : OrderAndQuoteClientDataMessage) : (encode message).length = 97 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LastCapacity.encode_length, AutomaticOrderFilterFlag.encode_length, ReceivedDeptId.encode_length, Persistence.encode_length, AccountType.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : OrderAndQuoteClientDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAndQuoteClientDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AutomaticOrderFilterFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReceivedDeptId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAndQuoteClientDataMessage

/-- Simple New Order Message: 29 bytes -/
structure SimpleNewOrderMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  clientDataId : BitVec 16
  orderId : BitVec 32
  side : Side
  price : BitVec 64
  orderQty : BitVec 32
  timeInForce : Alpha 1
  orderPlacement : BitVec 8
  deriving DecidableEq, Repr

namespace SimpleNewOrderMessage

def encode (message : SimpleNewOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (Alpha.encode message.timeInForce
    ++ (encodeUIntLE 1 message.orderPlacement))))))))

def decode (bytes : List UInt8) : Option (SimpleNewOrderMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (timeInForce, bytes) ← Alpha.decode 1 bytes
  let (orderPlacement, bytes) ← decodeUIntLE 1 bytes
  pure ({ requestId, securityCode, clientDataId, orderId, side, price, orderQty, timeInForce, orderPlacement }, bytes)

@[simp] theorem encode_length (message : SimpleNewOrderMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SimpleNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleNewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SimpleNewOrderMessage

/-- Simple New Order With Client Data Message: 118 bytes -/
structure SimpleNewOrderWithClientDataMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  orderId : BitVec 32
  side : Side
  price : BitVec 64
  orderQty : BitVec 32
  timeInForce : Alpha 1
  orderPlacement : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  accountBolsa : Alpha 16
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  automaticOrderFilterFlag : AutomaticOrderFilterFlag
  receivedDeptId : ReceivedDeptId
  persistence : Persistence
  accountType : AccountType
  selfMatchPreventionType : SelfMatchPreventionType
  clientDataReference : Alpha 15
  deriving DecidableEq, Repr

namespace SimpleNewOrderWithClientDataMessage

def encode (message : SimpleNewOrderWithClientDataMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (Alpha.encode message.timeInForce
    ++ (encodeUIntLE 1 message.orderPlacement
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.accountBolsa
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (AutomaticOrderFilterFlag.encode message.automaticOrderFilterFlag
    ++ (ReceivedDeptId.encode message.receivedDeptId
    ++ (Persistence.encode message.persistence
    ++ (AccountType.encode message.accountType
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.clientDataReference))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SimpleNewOrderWithClientDataMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (timeInForce, bytes) ← Alpha.decode 1 bytes
  let (orderPlacement, bytes) ← decodeUIntLE 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (accountBolsa, bytes) ← Alpha.decode 16 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (automaticOrderFilterFlag, bytes) ← AutomaticOrderFilterFlag.decode bytes
  let (receivedDeptId, bytes) ← ReceivedDeptId.decode bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (clientDataReference, bytes) ← Alpha.decode 15 bytes
  pure ({ requestId, securityCode, orderId, side, price, orderQty, timeInForce, orderPlacement, algorithmicTradeIndicator, clientId, accountBolsa, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, automaticOrderFilterFlag, receivedDeptId, persistence, accountType, selfMatchPreventionType, clientDataReference }, bytes)

@[simp] theorem encode_length (message : SimpleNewOrderWithClientDataMessage) : (encode message).length = 118 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, LastCapacity.encode_length, AutomaticOrderFilterFlag.encode_length, ReceivedDeptId.encode_length, Persistence.encode_length, AccountType.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : SimpleNewOrderWithClientDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SimpleNewOrderWithClientDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AutomaticOrderFilterFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReceivedDeptId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleNewOrderWithClientDataMessage

/-- Simple Order Modification Message: 27 bytes -/
structure SimpleOrderModificationMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  orderId : BitVec 32
  side : Side
  price : BitVec 64
  orderQty : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace SimpleOrderModificationMessage

def encode (message : SimpleOrderModificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 2 message.clientDataId))))))

def decode (bytes : List UInt8) : Option (SimpleOrderModificationMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ requestId, securityCode, orderId, side, price, orderQty, clientDataId }, bytes)

@[simp] theorem encode_length (message : SimpleOrderModificationMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : SimpleOrderModificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleOrderModificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SimpleOrderModificationMessage

/-- Simple Order Modification With Client Data Message: 116 bytes -/
structure SimpleOrderModificationWithClientDataMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  orderId : BitVec 32
  side : Side
  price : BitVec 64
  orderQty : BitVec 32
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  accountBolsa : Alpha 16
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  automaticOrderFilterFlag : AutomaticOrderFilterFlag
  receivedDeptId : ReceivedDeptId
  persistence : Persistence
  accountType : AccountType
  selfMatchPreventionType : SelfMatchPreventionType
  clientDataReference : Alpha 15
  deriving DecidableEq, Repr

namespace SimpleOrderModificationWithClientDataMessage

def encode (message : SimpleOrderModificationWithClientDataMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.accountBolsa
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (AutomaticOrderFilterFlag.encode message.automaticOrderFilterFlag
    ++ (ReceivedDeptId.encode message.receivedDeptId
    ++ (Persistence.encode message.persistence
    ++ (AccountType.encode message.accountType
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.clientDataReference))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SimpleOrderModificationWithClientDataMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (accountBolsa, bytes) ← Alpha.decode 16 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (automaticOrderFilterFlag, bytes) ← AutomaticOrderFilterFlag.decode bytes
  let (receivedDeptId, bytes) ← ReceivedDeptId.decode bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (clientDataReference, bytes) ← Alpha.decode 15 bytes
  pure ({ requestId, securityCode, orderId, side, price, orderQty, algorithmicTradeIndicator, clientId, accountBolsa, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, automaticOrderFilterFlag, receivedDeptId, persistence, accountType, selfMatchPreventionType, clientDataReference }, bytes)

@[simp] theorem encode_length (message : SimpleOrderModificationWithClientDataMessage) : (encode message).length = 116 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, LastCapacity.encode_length, AutomaticOrderFilterFlag.encode_length, ReceivedDeptId.encode_length, Persistence.encode_length, AccountType.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : SimpleOrderModificationWithClientDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SimpleOrderModificationWithClientDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AutomaticOrderFilterFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReceivedDeptId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleOrderModificationWithClientDataMessage

/-- Order Cancellation Request Message: 12 bytes -/
structure OrderCancellationRequestMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  orderId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancellationRequestMessage

def encode (message : OrderCancellationRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.orderId))

def decode (bytes : List UInt8) : Option (OrderCancellationRequestMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  pure ({ requestId, securityCode, orderId }, bytes)

@[simp] theorem encode_length (message : OrderCancellationRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancellationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancellationRequestMessage

/-- New Quote Message: 34 bytes -/
structure NewQuoteMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  clientDataId : BitVec 16
  bidSize1 : BitVec 32
  bidPx1 : BitVec 64
  askSize1 : BitVec 32
  askPx1 : BitVec 64
  deriving DecidableEq, Repr

namespace NewQuoteMessage

def encode (message : NewQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 4 message.bidSize1
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 4 message.askSize1
    ++ (encodeUIntLE 8 message.askPx1))))))

def decode (bytes : List UInt8) : Option (NewQuoteMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (bidSize1, bytes) ← decodeUIntLE 4 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askSize1, bytes) ← decodeUIntLE 4 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  pure ({ requestId, securityCode, clientDataId, bidSize1, bidPx1, askSize1, askPx1 }, bytes)

@[simp] theorem encode_length (message : NewQuoteMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NewQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewQuoteMessage

/-- Quote Modification Request Message: 26 bytes -/
structure QuoteModificationRequestMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  clientDataId : BitVec 16
  bidPx1 : BitVec 64
  askPx1 : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteModificationRequestMessage

def encode (message : QuoteModificationRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 8 message.askPx1))))

def decode (bytes : List UInt8) : Option (QuoteModificationRequestMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  pure ({ requestId, securityCode, clientDataId, bidPx1, askPx1 }, bytes)

@[simp] theorem encode_length (message : QuoteModificationRequestMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteModificationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteModificationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteModificationRequestMessage

/-- Quote Cancellation Request Message: 10 bytes -/
structure QuoteCancellationRequestMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteCancellationRequestMessage

def encode (message : QuoteCancellationRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 message.clientDataId))

def decode (bytes : List UInt8) : Option (QuoteCancellationRequestMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ requestId, securityCode, clientDataId }, bytes)

@[simp] theorem encode_length (message : QuoteCancellationRequestMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancellationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancellationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteCancellationRequestMessage

/-- Mass Orderquote Cancellation Message: 38 bytes -/
structure MassOrderquoteCancellationMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  side : Side
  issuer : Alpha 12
  accountBolsa : Alpha 16
  orderOrQuoteCancel : OrderOrQuoteCancel
  deriving DecidableEq, Repr

namespace MassOrderquoteCancellationMessage

def encode (message : MassOrderquoteCancellationMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Side.encode message.side
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.accountBolsa
    ++ (OrderOrQuoteCancel.encode message.orderOrQuoteCancel)))))

def decode (bytes : List UInt8) : Option (MassOrderquoteCancellationMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (issuer, bytes) ← Alpha.decode 12 bytes
  let (accountBolsa, bytes) ← Alpha.decode 16 bytes
  let (orderOrQuoteCancel, bytes) ← OrderOrQuoteCancel.decode bytes
  pure ({ requestId, securityCode, side, issuer, accountBolsa, orderOrQuoteCancel }, bytes)

@[simp] theorem encode_length (message : MassOrderquoteCancellationMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, OrderOrQuoteCancel.encode_length]

theorem encode_length_pos (message : MassOrderquoteCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassOrderquoteCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [OrderOrQuoteCancel.decode_encode, some_bind]
  rfl

end MassOrderquoteCancellationMessage

/-- Order And Quote Client Data Parameters Ack Nack Message: 102 bytes -/
structure OrderAndQuoteClientDataParametersAckNackMessage where
  sequenceNumber : BitVec 32
  requestId : BitVec 32
  status : BitVec 8
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  accountBolsa : Alpha 16
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  automaticOrderFilterFlag : AutomaticOrderFilterFlag
  receivedDeptId : ReceivedDeptId
  persistence : Persistence
  accountType : AccountType
  selfMatchPreventionType : SelfMatchPreventionType
  clientDataReference : Alpha 15
  deriving DecidableEq, Repr

namespace OrderAndQuoteClientDataParametersAckNackMessage

def encode (message : OrderAndQuoteClientDataParametersAckNackMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 1 message.status
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.accountBolsa
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (AutomaticOrderFilterFlag.encode message.automaticOrderFilterFlag
    ++ (ReceivedDeptId.encode message.receivedDeptId
    ++ (Persistence.encode message.persistence
    ++ (AccountType.encode message.accountType
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.clientDataReference))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAndQuoteClientDataParametersAckNackMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (accountBolsa, bytes) ← Alpha.decode 16 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (automaticOrderFilterFlag, bytes) ← AutomaticOrderFilterFlag.decode bytes
  let (receivedDeptId, bytes) ← ReceivedDeptId.decode bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (clientDataReference, bytes) ← Alpha.decode 15 bytes
  pure ({ sequenceNumber, requestId, status, clientDataId, algorithmicTradeIndicator, clientId, accountBolsa, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, automaticOrderFilterFlag, receivedDeptId, persistence, accountType, selfMatchPreventionType, clientDataReference }, bytes)

@[simp] theorem encode_length (message : OrderAndQuoteClientDataParametersAckNackMessage) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LastCapacity.encode_length, AutomaticOrderFilterFlag.encode_length, ReceivedDeptId.encode_length, Persistence.encode_length, AccountType.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : OrderAndQuoteClientDataParametersAckNackMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAndQuoteClientDataParametersAckNackMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AutomaticOrderFilterFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReceivedDeptId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAndQuoteClientDataParametersAckNackMessage

/-- Simple Order Status Message: 62 bytes -/
structure SimpleOrderStatusMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  side : Side
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ordRejReason : OrdRejReason
  execType : ExecType
  requestId : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace SimpleOrderStatusMessage

def encode (message : SimpleOrderStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (OrdRejReason.encode message.ordRejReason
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleOrderStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← OrdRejReason.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, entryDate, side, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ordRejReason, execType, requestId, clientDataId }, bytes)

@[simp] theorem encode_length (message : SimpleOrderStatusMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, OrdStatus.encode_length, OrdRejReason.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : SimpleOrderStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleOrderStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdRejReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SimpleOrderStatusMessage

/-- Quote Status Message: 92 bytes -/
structure QuoteStatusMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  secondaryOrderId2 : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ordRejReason : OrdRejReason
  execType : ExecType
  orderId2 : BitVec 32
  secondaryExecId2 : BitVec 32
  orderQty2 : BitVec 32
  ordStatus2 : OrdStatus2
  ordRejReason2 : OrdRejReason2
  execType2 : ExecType2
  requestId : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteStatusMessage

def encode (message : QuoteStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (OrdRejReason.encode message.ordRejReason
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 4 message.orderId2
    ++ (encodeUIntLE 4 message.secondaryExecId2
    ++ (encodeUIntLE 4 message.orderQty2
    ++ (OrdStatus2.encode message.ordStatus2
    ++ (OrdRejReason2.encode message.ordRejReason2
    ++ (ExecType2.encode message.execType2
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (QuoteStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← OrdRejReason.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (orderId2, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId2, bytes) ← decodeUIntLE 4 bytes
  let (orderQty2, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus2, bytes) ← OrdStatus2.decode bytes
  let (ordRejReason2, bytes) ← OrdRejReason2.decode bytes
  let (execType2, bytes) ← ExecType2.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, secondaryOrderId2, priority, price, displayQty, priority2, price2, displayQty2, orderId, secondaryExecId, orderQty, ordStatus, ordRejReason, execType, orderId2, secondaryExecId2, orderQty2, ordStatus2, ordRejReason2, execType2, requestId, clientDataId }, bytes)

@[simp] theorem encode_length (message : QuoteStatusMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrdStatus.encode_length, OrdRejReason.encode_length, ExecType.encode_length, OrdStatus2.encode_length, OrdRejReason2.encode_length, ExecType2.encode_length]

theorem encode_length_pos (message : QuoteStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : QuoteStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdRejReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdRejReason2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteStatusMessage

/-- Order Cancel Reject Message: 19 bytes -/
structure OrderCancelRejectMessage where
  sequenceNumber : BitVec 32
  transactionDateAndTime : BitVec 64
  orderId : BitVec 32
  ordStatus : OrdStatus
  cxlRejResponseTo : CxlRejResponseTo
  cxlRejReason : CxlRejReason
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.orderId
    ++ (OrdStatus.encode message.ordStatus
    ++ (CxlRejResponseTo.encode message.cxlRejResponseTo
    ++ (CxlRejReason.encode message.cxlRejReason)))))

def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (cxlRejResponseTo, bytes) ← CxlRejResponseTo.decode bytes
  let (cxlRejReason, bytes) ← CxlRejReason.decode bytes
  pure ({ sequenceNumber, transactionDateAndTime, orderId, ordStatus, cxlRejResponseTo, cxlRejReason }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrdStatus.encode_length, CxlRejResponseTo.encode_length, CxlRejReason.encode_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CxlRejResponseTo.decode_encode, some_bind]
  dsimp only
  rw [CxlRejReason.decode_encode, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Mass Orderquote Cancellation Completion Message: 18 bytes -/
structure MassOrderquoteCancellationCompletionMessage where
  sequenceNumber : BitVec 32
  transactionDateAndTime : BitVec 64
  tradingUnit : BitVec 8
  orderOrQuoteCancel : OrderOrQuoteCancel
  requestId : BitVec 32
  deriving DecidableEq, Repr

namespace MassOrderquoteCancellationCompletionMessage

def encode (message : MassOrderquoteCancellationCompletionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.tradingUnit
    ++ (OrderOrQuoteCancel.encode message.orderOrQuoteCancel
    ++ (encodeUIntLE 4 message.requestId))))

def decode (bytes : List UInt8) : Option (MassOrderquoteCancellationCompletionMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingUnit, bytes) ← decodeUIntLE 1 bytes
  let (orderOrQuoteCancel, bytes) ← OrderOrQuoteCancel.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, transactionDateAndTime, tradingUnit, orderOrQuoteCancel, requestId }, bytes)

@[simp] theorem encode_length (message : MassOrderquoteCancellationCompletionMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderOrQuoteCancel.encode_length]

theorem encode_length_pos (message : MassOrderquoteCancellationCompletionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassOrderquoteCancellationCompletionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderOrQuoteCancel.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MassOrderquoteCancellationCompletionMessage

/-- Mass Orderquote Cancellation Reject Message: 14 bytes -/
structure MassOrderquoteCancellationRejectMessage where
  sequenceNumber : BitVec 32
  transactionDateAndTime : BitVec 64
  tradingUnit : BitVec 8
  massCancelRejectReason : MassCancelRejectReason
  deriving DecidableEq, Repr

namespace MassOrderquoteCancellationRejectMessage

def encode (message : MassOrderquoteCancellationRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.tradingUnit
    ++ (MassCancelRejectReason.encode message.massCancelRejectReason)))

def decode (bytes : List UInt8) : Option (MassOrderquoteCancellationRejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingUnit, bytes) ← decodeUIntLE 1 bytes
  let (massCancelRejectReason, bytes) ← MassCancelRejectReason.decode bytes
  pure ({ sequenceNumber, transactionDateAndTime, tradingUnit, massCancelRejectReason }, bytes)

@[simp] theorem encode_length (message : MassOrderquoteCancellationRejectMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MassCancelRejectReason.encode_length]

theorem encode_length_pos (message : MassOrderquoteCancellationRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassOrderquoteCancellationRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [MassCancelRejectReason.decode_encode, some_bind]
  rfl

end MassOrderquoteCancellationRejectMessage

/-- Business Message Reject Message: 79 bytes -/
structure BusinessMessageRejectMessage where
  sequenceNumber : BitVec 32
  transactionDateAndTime : BitVec 64
  refMsgType : BitVec 8
  businessRejectReason : BitVec 8
  textC65 : Alpha 65
  deriving DecidableEq, Repr

namespace BusinessMessageRejectMessage

def encode (message : BusinessMessageRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.refMsgType
    ++ (encodeUIntLE 1 message.businessRejectReason
    ++ (Alpha.encode message.textC65))))

def decode (bytes : List UInt8) : Option (BusinessMessageRejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (refMsgType, bytes) ← decodeUIntLE 1 bytes
  let (businessRejectReason, bytes) ← decodeUIntLE 1 bytes
  let (textC65, bytes) ← Alpha.decode 65 bytes
  pure ({ sequenceNumber, transactionDateAndTime, refMsgType, businessRejectReason, textC65 }, bytes)

@[simp] theorem encode_length (message : BusinessMessageRejectMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BusinessMessageRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessMessageRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BusinessMessageRejectMessage

/-- Execution Private Information 2 Legs Message: 145 bytes -/
structure ExecutionPrivateInformation2LegsMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  orderId2 : BitVec 32
  secondaryExecId2 : BitVec 32
  orderQty2 : BitVec 32
  ordStatus2 : OrdStatus2
  ccpCode2 : CcpCode2
  aggressorIndicator2 : AggressorIndicator2
  requestId2 : BitVec 32
  clientDataId2U2 : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionPrivateInformation2LegsMessage

def encode (message : ExecutionPrivateInformation2LegsMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 4 message.orderId2
    ++ (encodeUIntLE 4 message.secondaryExecId2
    ++ (encodeUIntLE 4 message.orderQty2
    ++ (OrdStatus2.encode message.ordStatus2
    ++ (CcpCode2.encode message.ccpCode2
    ++ (AggressorIndicator2.encode message.aggressorIndicator2
    ++ (encodeUIntLE 4 message.requestId2
    ++ (encodeUIntLE 2 message.clientDataId2U2)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionPrivateInformation2LegsMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (orderId2, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId2, bytes) ← decodeUIntLE 4 bytes
  let (orderQty2, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus2, bytes) ← OrdStatus2.decode bytes
  let (ccpCode2, bytes) ← CcpCode2.decode bytes
  let (aggressorIndicator2, bytes) ← AggressorIndicator2.decode bytes
  let (requestId2, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId2U2, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, orderId2, secondaryExecId2, orderQty2, ordStatus2, ccpCode2, aggressorIndicator2, requestId2, clientDataId2U2 }, bytes)

@[simp] theorem encode_length (message : ExecutionPrivateInformation2LegsMessage) : (encode message).length = 145 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length, OrdStatus2.encode_length, CcpCode2.encode_length, AggressorIndicator2.encode_length]

theorem encode_length_pos (message : ExecutionPrivateInformation2LegsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionPrivateInformation2LegsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionPrivateInformation2LegsMessage

/-- Trade Trade Amendment Or Cancellation 1 Leg Buy Private Information Message: 317 bytes -/
structure TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  lastChangeFlagB1 : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  volumeFloat : BitVec 64
  sicavFundCounterpartySide : SicavFundCounterpartySide
  amendedTradeType : AmendedTradeType
  execRefId : BitVec 32
  amendedTradeDate : BitVec 32
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  accountBolsa : Alpha 16
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  automaticOrderFilterFlag : AutomaticOrderFilterFlag
  receivedDeptId : ReceivedDeptId
  persistence : Persistence
  accountType : AccountType
  selfMatchPreventionType : SelfMatchPreventionType
  member : Alpha 4
  trader : Alpha 3
  subMember : Alpha 1
  crossId : BitVec 32
  bolsaCode : Alpha 1
  csdbic : Alpha 11
  participant : Alpha 11
  ctaLiq : Alpha 35
  ccv : Alpha 20
  orderSecurityCode : BitVec 32
  externalMember : Alpha 4
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage

def encode (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 1 message.lastChangeFlagB1
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (encodeUIntLE 8 message.volumeFloat
    ++ (SicavFundCounterpartySide.encode message.sicavFundCounterpartySide
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.accountBolsa
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (AutomaticOrderFilterFlag.encode message.automaticOrderFilterFlag
    ++ (ReceivedDeptId.encode message.receivedDeptId
    ++ (Persistence.encode message.persistence
    ++ (AccountType.encode message.accountType
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.member
    ++ (Alpha.encode message.trader
    ++ (Alpha.encode message.subMember
    ++ (encodeUIntLE 4 message.crossId
    ++ (Alpha.encode message.bolsaCode
    ++ (Alpha.encode message.csdbic
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.ctaLiq
    ++ (Alpha.encode message.ccv
    ++ (encodeUIntLE 4 message.orderSecurityCode
    ++ (Alpha.encode message.externalMember))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (lastChangeFlagB1, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (volumeFloat, bytes) ← decodeUIntLE 8 bytes
  let (sicavFundCounterpartySide, bytes) ← SicavFundCounterpartySide.decode bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (accountBolsa, bytes) ← Alpha.decode 16 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (automaticOrderFilterFlag, bytes) ← AutomaticOrderFilterFlag.decode bytes
  let (receivedDeptId, bytes) ← ReceivedDeptId.decode bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (member, bytes) ← Alpha.decode 4 bytes
  let (trader, bytes) ← Alpha.decode 3 bytes
  let (subMember, bytes) ← Alpha.decode 1 bytes
  let (crossId, bytes) ← decodeUIntLE 4 bytes
  let (bolsaCode, bytes) ← Alpha.decode 1 bytes
  let (csdbic, bytes) ← Alpha.decode 11 bytes
  let (participant, bytes) ← Alpha.decode 11 bytes
  let (ctaLiq, bytes) ← Alpha.decode 35 bytes
  let (ccv, bytes) ← Alpha.decode 20 bytes
  let (orderSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (externalMember, bytes) ← Alpha.decode 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, lastChangeFlagB1, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, publishDateAndTime, tradeDate, tradeSessionDate, volumeFloat, sicavFundCounterpartySide, amendedTradeType, execRefId, amendedTradeDate, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, algorithmicTradeIndicator, clientId, accountBolsa, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, automaticOrderFilterFlag, receivedDeptId, persistence, accountType, selfMatchPreventionType, member, trader, subMember, crossId, bolsaCode, csdbic, participant, ctaLiq, ccv, orderSecurityCode, externalMember }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) : (encode message).length = 317 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, SicavFundCounterpartySide.encode_length, AmendedTradeType.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length, LastCapacity.encode_length, AutomaticOrderFilterFlag.encode_length, ReceivedDeptId.encode_length, Persistence.encode_length, AccountType.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BencrfptFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreTradeTransparencyWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SicavFundCounterpartySide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AutomaticOrderFilterFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReceivedDeptId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage

/-- Trade Trade Amendment Or Cancellation 1 Leg Sell Private Information Message: 317 bytes -/
structure TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  lastChangeFlagB1 : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  volumeFloat : BitVec 64
  sicavFundCounterpartySide : SicavFundCounterpartySide
  amendedTradeType : AmendedTradeType
  execRefId : BitVec 32
  amendedTradeDate : BitVec 32
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  accountBolsa : Alpha 16
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  automaticOrderFilterFlag : AutomaticOrderFilterFlag
  receivedDeptId : ReceivedDeptId
  persistence : Persistence
  accountType : AccountType
  selfMatchPreventionType : SelfMatchPreventionType
  member : Alpha 4
  trader : Alpha 3
  subMember : Alpha 1
  crossId : BitVec 32
  bolsaCode : Alpha 1
  csdbic : Alpha 11
  participant : Alpha 11
  ctaLiq : Alpha 35
  ccv : Alpha 20
  orderSecurityCode : BitVec 32
  externalMember : Alpha 4
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage

def encode (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 1 message.lastChangeFlagB1
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (encodeUIntLE 8 message.volumeFloat
    ++ (SicavFundCounterpartySide.encode message.sicavFundCounterpartySide
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.accountBolsa
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (AutomaticOrderFilterFlag.encode message.automaticOrderFilterFlag
    ++ (ReceivedDeptId.encode message.receivedDeptId
    ++ (Persistence.encode message.persistence
    ++ (AccountType.encode message.accountType
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.member
    ++ (Alpha.encode message.trader
    ++ (Alpha.encode message.subMember
    ++ (encodeUIntLE 4 message.crossId
    ++ (Alpha.encode message.bolsaCode
    ++ (Alpha.encode message.csdbic
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.ctaLiq
    ++ (Alpha.encode message.ccv
    ++ (encodeUIntLE 4 message.orderSecurityCode
    ++ (Alpha.encode message.externalMember))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (lastChangeFlagB1, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (volumeFloat, bytes) ← decodeUIntLE 8 bytes
  let (sicavFundCounterpartySide, bytes) ← SicavFundCounterpartySide.decode bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (accountBolsa, bytes) ← Alpha.decode 16 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (automaticOrderFilterFlag, bytes) ← AutomaticOrderFilterFlag.decode bytes
  let (receivedDeptId, bytes) ← ReceivedDeptId.decode bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (member, bytes) ← Alpha.decode 4 bytes
  let (trader, bytes) ← Alpha.decode 3 bytes
  let (subMember, bytes) ← Alpha.decode 1 bytes
  let (crossId, bytes) ← decodeUIntLE 4 bytes
  let (bolsaCode, bytes) ← Alpha.decode 1 bytes
  let (csdbic, bytes) ← Alpha.decode 11 bytes
  let (participant, bytes) ← Alpha.decode 11 bytes
  let (ctaLiq, bytes) ← Alpha.decode 35 bytes
  let (ccv, bytes) ← Alpha.decode 20 bytes
  let (orderSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (externalMember, bytes) ← Alpha.decode 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, lastChangeFlagB1, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, publishDateAndTime, tradeDate, tradeSessionDate, volumeFloat, sicavFundCounterpartySide, amendedTradeType, execRefId, amendedTradeDate, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, algorithmicTradeIndicator, clientId, accountBolsa, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, automaticOrderFilterFlag, receivedDeptId, persistence, accountType, selfMatchPreventionType, member, trader, subMember, crossId, bolsaCode, csdbic, participant, ctaLiq, ccv, orderSecurityCode, externalMember }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) : (encode message).length = 317 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, SicavFundCounterpartySide.encode_length, AmendedTradeType.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length, LastCapacity.encode_length, AutomaticOrderFilterFlag.encode_length, ReceivedDeptId.encode_length, Persistence.encode_length, AccountType.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BencrfptFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreTradeTransparencyWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SicavFundCounterpartySide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AutomaticOrderFilterFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReceivedDeptId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage

/-- Trade Trade Amendment Or Cancellation 2 Legs Private Information Message: 536 bytes -/
structure TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  lastChangeFlagB1 : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  volumeFloat : BitVec 64
  sicavFundCounterpartySide : SicavFundCounterpartySide
  amendedTradeType : AmendedTradeType
  execRefId : BitVec 32
  amendedTradeDate : BitVec 32
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  accountBolsa : Alpha 16
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  automaticOrderFilterFlag : AutomaticOrderFilterFlag
  receivedDeptId : ReceivedDeptId
  persistence : Persistence
  accountType : AccountType
  selfMatchPreventionType : SelfMatchPreventionType
  member : Alpha 4
  trader : Alpha 3
  subMember : Alpha 1
  crossId : BitVec 32
  bolsaCode : Alpha 1
  csdbic : Alpha 11
  participant : Alpha 11
  ctaLiq : Alpha 35
  ccv : Alpha 20
  orderSecurityCode : BitVec 32
  externalMember : Alpha 4
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  orderId2 : BitVec 32
  secondaryExecId2 : BitVec 32
  orderQty2 : BitVec 32
  ordStatus2 : OrdStatus2
  ccpCode2 : CcpCode2
  aggressorIndicator2 : AggressorIndicator2
  requestId2 : BitVec 32
  clientDataId2U2 : BitVec 16
  algorithmicTradeIndicator2 : BitVec 8
  clientId2 : BitVec 32
  accountBolsa2 : Alpha 16
  account2 : Alpha 5
  deaFlag2 : BitVec 8
  decisorId2 : BitVec 32
  executorId2 : BitVec 32
  liquidityProvisionActivity2 : BitVec 8
  giveInMember2 : Alpha 4
  firmMnemonic2 : Alpha 10
  allocText2 : Alpha 18
  lastCapacity2 : LastCapacity2
  selfMatchPreventionId2 : BitVec 16
  automaticOrderFilterFlag2 : AutomaticOrderFilterFlag2
  receivedDeptId2 : ReceivedDeptId2
  persistence2 : Persistence2
  accountType2 : AccountType2
  selfMatchPreventionType2 : SelfMatchPreventionType2
  member2 : Alpha 4
  trader2 : Alpha 3
  subMember2 : Alpha 1
  crossId2 : BitVec 32
  bolsaCode2 : Alpha 1
  csdbic2 : Alpha 11
  participant2 : Alpha 11
  ctaLiq2 : Alpha 35
  ccv2 : Alpha 20
  orderSecurityCode2 : BitVec 32
  externalMember2 : Alpha 4
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage

def encode (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 1 message.lastChangeFlagB1
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (encodeUIntLE 8 message.volumeFloat
    ++ (SicavFundCounterpartySide.encode message.sicavFundCounterpartySide
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.accountBolsa
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (AutomaticOrderFilterFlag.encode message.automaticOrderFilterFlag
    ++ (ReceivedDeptId.encode message.receivedDeptId
    ++ (Persistence.encode message.persistence
    ++ (AccountType.encode message.accountType
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.member
    ++ (Alpha.encode message.trader
    ++ (Alpha.encode message.subMember
    ++ (encodeUIntLE 4 message.crossId
    ++ (Alpha.encode message.bolsaCode
    ++ (Alpha.encode message.csdbic
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.ctaLiq
    ++ (Alpha.encode message.ccv
    ++ (encodeUIntLE 4 message.orderSecurityCode
    ++ (Alpha.encode message.externalMember
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 4 message.orderId2
    ++ (encodeUIntLE 4 message.secondaryExecId2
    ++ (encodeUIntLE 4 message.orderQty2
    ++ (OrdStatus2.encode message.ordStatus2
    ++ (CcpCode2.encode message.ccpCode2
    ++ (AggressorIndicator2.encode message.aggressorIndicator2
    ++ (encodeUIntLE 4 message.requestId2
    ++ (encodeUIntLE 2 message.clientDataId2U2
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator2
    ++ (encodeUIntLE 4 message.clientId2
    ++ (Alpha.encode message.accountBolsa2
    ++ (Alpha.encode message.account2
    ++ (encodeUIntLE 1 message.deaFlag2
    ++ (encodeUIntLE 4 message.decisorId2
    ++ (encodeUIntLE 4 message.executorId2
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity2
    ++ (Alpha.encode message.giveInMember2
    ++ (Alpha.encode message.firmMnemonic2
    ++ (Alpha.encode message.allocText2
    ++ (LastCapacity2.encode message.lastCapacity2
    ++ (encodeUIntLE 2 message.selfMatchPreventionId2
    ++ (AutomaticOrderFilterFlag2.encode message.automaticOrderFilterFlag2
    ++ (ReceivedDeptId2.encode message.receivedDeptId2
    ++ (Persistence2.encode message.persistence2
    ++ (AccountType2.encode message.accountType2
    ++ (SelfMatchPreventionType2.encode message.selfMatchPreventionType2
    ++ (Alpha.encode message.member2
    ++ (Alpha.encode message.trader2
    ++ (Alpha.encode message.subMember2
    ++ (encodeUIntLE 4 message.crossId2
    ++ (Alpha.encode message.bolsaCode2
    ++ (Alpha.encode message.csdbic2
    ++ (Alpha.encode message.participant2
    ++ (Alpha.encode message.ctaLiq2
    ++ (Alpha.encode message.ccv2
    ++ (encodeUIntLE 4 message.orderSecurityCode2
    ++ (Alpha.encode message.externalMember2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (lastChangeFlagB1, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (volumeFloat, bytes) ← decodeUIntLE 8 bytes
  let (sicavFundCounterpartySide, bytes) ← SicavFundCounterpartySide.decode bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (accountBolsa, bytes) ← Alpha.decode 16 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (automaticOrderFilterFlag, bytes) ← AutomaticOrderFilterFlag.decode bytes
  let (receivedDeptId, bytes) ← ReceivedDeptId.decode bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (member, bytes) ← Alpha.decode 4 bytes
  let (trader, bytes) ← Alpha.decode 3 bytes
  let (subMember, bytes) ← Alpha.decode 1 bytes
  let (crossId, bytes) ← decodeUIntLE 4 bytes
  let (bolsaCode, bytes) ← Alpha.decode 1 bytes
  let (csdbic, bytes) ← Alpha.decode 11 bytes
  let (participant, bytes) ← Alpha.decode 11 bytes
  let (ctaLiq, bytes) ← Alpha.decode 35 bytes
  let (ccv, bytes) ← Alpha.decode 20 bytes
  let (orderSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (externalMember, bytes) ← Alpha.decode 4 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (orderId2, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId2, bytes) ← decodeUIntLE 4 bytes
  let (orderQty2, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus2, bytes) ← OrdStatus2.decode bytes
  let (ccpCode2, bytes) ← CcpCode2.decode bytes
  let (aggressorIndicator2, bytes) ← AggressorIndicator2.decode bytes
  let (requestId2, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId2U2, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator2, bytes) ← decodeUIntLE 1 bytes
  let (clientId2, bytes) ← decodeUIntLE 4 bytes
  let (accountBolsa2, bytes) ← Alpha.decode 16 bytes
  let (account2, bytes) ← Alpha.decode 5 bytes
  let (deaFlag2, bytes) ← decodeUIntLE 1 bytes
  let (decisorId2, bytes) ← decodeUIntLE 4 bytes
  let (executorId2, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity2, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember2, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic2, bytes) ← Alpha.decode 10 bytes
  let (allocText2, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity2, bytes) ← LastCapacity2.decode bytes
  let (selfMatchPreventionId2, bytes) ← decodeUIntLE 2 bytes
  let (automaticOrderFilterFlag2, bytes) ← AutomaticOrderFilterFlag2.decode bytes
  let (receivedDeptId2, bytes) ← ReceivedDeptId2.decode bytes
  let (persistence2, bytes) ← Persistence2.decode bytes
  let (accountType2, bytes) ← AccountType2.decode bytes
  let (selfMatchPreventionType2, bytes) ← SelfMatchPreventionType2.decode bytes
  let (member2, bytes) ← Alpha.decode 4 bytes
  let (trader2, bytes) ← Alpha.decode 3 bytes
  let (subMember2, bytes) ← Alpha.decode 1 bytes
  let (crossId2, bytes) ← decodeUIntLE 4 bytes
  let (bolsaCode2, bytes) ← Alpha.decode 1 bytes
  let (csdbic2, bytes) ← Alpha.decode 11 bytes
  let (participant2, bytes) ← Alpha.decode 11 bytes
  let (ctaLiq2, bytes) ← Alpha.decode 35 bytes
  let (ccv2, bytes) ← Alpha.decode 20 bytes
  let (orderSecurityCode2, bytes) ← decodeUIntLE 4 bytes
  let (externalMember2, bytes) ← Alpha.decode 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, lastChangeFlagB1, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, publishDateAndTime, tradeDate, tradeSessionDate, volumeFloat, sicavFundCounterpartySide, amendedTradeType, execRefId, amendedTradeDate, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, algorithmicTradeIndicator, clientId, accountBolsa, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, automaticOrderFilterFlag, receivedDeptId, persistence, accountType, selfMatchPreventionType, member, trader, subMember, crossId, bolsaCode, csdbic, participant, ctaLiq, ccv, orderSecurityCode, externalMember, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, orderId2, secondaryExecId2, orderQty2, ordStatus2, ccpCode2, aggressorIndicator2, requestId2, clientDataId2U2, algorithmicTradeIndicator2, clientId2, accountBolsa2, account2, deaFlag2, decisorId2, executorId2, liquidityProvisionActivity2, giveInMember2, firmMnemonic2, allocText2, lastCapacity2, selfMatchPreventionId2, automaticOrderFilterFlag2, receivedDeptId2, persistence2, accountType2, selfMatchPreventionType2, member2, trader2, subMember2, crossId2, bolsaCode2, csdbic2, participant2, ctaLiq2, ccv2, orderSecurityCode2, externalMember2 }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) : (encode message).length = 536 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, SicavFundCounterpartySide.encode_length, AmendedTradeType.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length, LastCapacity.encode_length, AutomaticOrderFilterFlag.encode_length, ReceivedDeptId.encode_length, Persistence.encode_length, AccountType.encode_length, SelfMatchPreventionType.encode_length, OrdStatus2.encode_length, CcpCode2.encode_length, AggressorIndicator2.encode_length, LastCapacity2.encode_length, AutomaticOrderFilterFlag2.encode_length, ReceivedDeptId2.encode_length, Persistence2.encode_length, AccountType2.encode_length, SelfMatchPreventionType2.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BencrfptFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreTradeTransparencyWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SicavFundCounterpartySide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AutomaticOrderFilterFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReceivedDeptId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AutomaticOrderFilterFlag2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReceivedDeptId2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage

/-- Execution Private Information 1 Leg Buy Market Order Message: 125 bytes -/
structure ExecutionPrivateInformation1LegBuyMarketOrderMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  retailFlag2 : BitVec 8
  deriving DecidableEq, Repr

namespace ExecutionPrivateInformation1LegBuyMarketOrderMessage

def encode (message : ExecutionPrivateInformation1LegBuyMarketOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 1 message.retailFlag2))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionPrivateInformation1LegBuyMarketOrderMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag2, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, retailFlag2 }, bytes)

@[simp] theorem encode_length (message : ExecutionPrivateInformation1LegBuyMarketOrderMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length]

theorem encode_length_pos (message : ExecutionPrivateInformation1LegBuyMarketOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionPrivateInformation1LegBuyMarketOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionPrivateInformation1LegBuyMarketOrderMessage

/-- Execution Private Information 1 Leg Sell Market Order Message: 125 bytes -/
structure ExecutionPrivateInformation1LegSellMarketOrderMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  buyerBolsaCode : BuyerBolsaCode
  settlDate : BitVec 32
  transactionCategory : TransactionCategory
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  retailFlag : BitVec 8
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  orderId2 : BitVec 32
  secondaryExecId2 : BitVec 32
  orderQty2 : BitVec 32
  ordStatus2 : OrdStatus2
  ccpCode2 : CcpCode2
  aggressorIndicator2 : AggressorIndicator2
  requestId2 : BitVec 32
  clientDataId2B2 : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionPrivateInformation1LegSellMarketOrderMessage

def encode (message : ExecutionPrivateInformation1LegSellMarketOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (BuyerBolsaCode.encode message.buyerBolsaCode
    ++ (encodeUIntLE 4 message.settlDate
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 1 message.retailFlag
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 4 message.orderId2
    ++ (encodeUIntLE 4 message.secondaryExecId2
    ++ (encodeUIntLE 4 message.orderQty2
    ++ (OrdStatus2.encode message.ordStatus2
    ++ (CcpCode2.encode message.ccpCode2
    ++ (AggressorIndicator2.encode message.aggressorIndicator2
    ++ (encodeUIntLE 4 message.requestId2
    ++ (encodeUIntLE 2 message.clientDataId2B2))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionPrivateInformation1LegSellMarketOrderMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (buyerBolsaCode, bytes) ← BuyerBolsaCode.decode bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (retailFlag, bytes) ← decodeUIntLE 1 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (orderId2, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId2, bytes) ← decodeUIntLE 4 bytes
  let (orderQty2, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus2, bytes) ← OrdStatus2.decode bytes
  let (ccpCode2, bytes) ← CcpCode2.decode bytes
  let (aggressorIndicator2, bytes) ← AggressorIndicator2.decode bytes
  let (requestId2, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId2B2, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, buyerBolsaCode, settlDate, transactionCategory, secondaryOrderId, entryDate, priority, price, displayQty, retailFlag, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, orderId2, secondaryExecId2, orderQty2, ordStatus2, ccpCode2, aggressorIndicator2, requestId2, clientDataId2B2 }, bytes)

@[simp] theorem encode_length (message : ExecutionPrivateInformation1LegSellMarketOrderMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, BuyerBolsaCode.encode_length, TransactionCategory.encode_length, OrdStatus2.encode_length, CcpCode2.encode_length, AggressorIndicator2.encode_length]

theorem encode_length_pos (message : ExecutionPrivateInformation1LegSellMarketOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionPrivateInformation1LegSellMarketOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerBolsaCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionPrivateInformation1LegSellMarketOrderMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | logonResponseMessage (message : LogonResponseMessage) -- 8
  | logoutResponseMessage (message : LogoutResponseMessage) -- 11
  | heartbeatMessage (message : HeartbeatMessage) -- 48
  | networkStatusMessage (message : NetworkStatusMessage) -- 10
  | logonMessage (message : LogonMessage) -- 65
  | rejectMessage (message : RejectMessage) -- 13
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 104
  | newsMessage (message : NewsMessage) -- 66
  | securityListCancellationReportMessage (message : SecurityListCancellationReportMessage) -- 120
  | statisticsMessage (message : StatisticsMessage) -- 132
  | securityListMessage (message : SecurityListMessage) -- 121
  | securityListUpdateReportMessage (message : SecurityListUpdateReportMessage) -- 128
  | securityStatusMessage (message : SecurityStatusMessage) -- 102
  | orderBookClearMessage (message : OrderBookClearMessage) -- 129
  | orderMarketPreTransparencyInformationMessage (message : OrderMarketPreTransparencyInformationMessage) -- 3
  | quoteMarketPreTransparencyInformationMessage (message : QuoteMarketPreTransparencyInformationMessage) -- 7
  | orderCancellationMarketMemberMessage (message : OrderCancellationMarketMemberMessage) -- 1
  | quoteCancellationMarketMemberMessage (message : QuoteCancellationMarketMemberMessage) -- 5
  | tradeMarketPostTransparencyInformationTopofbookMessage (message : TradeMarketPostTransparencyInformationTopofbookMessage) -- 16
  | tradeTradeAmendmentOrCancellationMessage (message : TradeTradeAmendmentOrCancellationMessage) -- 24
  | tradeMarketPostTransparencyInformationFullDepthMessage (message : TradeMarketPostTransparencyInformationFullDepthMessage) -- 17
  | topofbookMessage (message : TopofbookMessage) -- 130
  | orderAndQuoteClientDataMessage (message : OrderAndQuoteClientDataMessage) -- 111
  | simpleNewOrderMessage (message : SimpleNewOrderMessage) -- 68
  | simpleNewOrderWithClientDataMessage (message : SimpleNewOrderWithClientDataMessage) -- 69
  | simpleOrderModificationMessage (message : SimpleOrderModificationMessage) -- 71
  | simpleOrderModificationWithClientDataMessage (message : SimpleOrderModificationWithClientDataMessage) -- 72
  | orderCancellationRequestMessage (message : OrderCancellationRequestMessage) -- 70
  | newQuoteMessage (message : NewQuoteMessage) -- 83
  | quoteModificationRequestMessage (message : QuoteModificationRequestMessage) -- 97
  | quoteCancellationRequestMessage (message : QuoteCancellationRequestMessage) -- 90
  | massOrderquoteCancellationMessage (message : MassOrderquoteCancellationMessage) -- 113
  | orderAndQuoteClientDataParametersAckNackMessage (message : OrderAndQuoteClientDataParametersAckNackMessage) -- 135
  | simpleOrderStatusMessage (message : SimpleOrderStatusMessage) -- 2
  | quoteStatusMessage (message : QuoteStatusMessage) -- 6
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- 57
  | massOrderquoteCancellationCompletionMessage (message : MassOrderquoteCancellationCompletionMessage) -- 114
  | massOrderquoteCancellationRejectMessage (message : MassOrderquoteCancellationRejectMessage) -- 115
  | businessMessageRejectMessage (message : BusinessMessageRejectMessage) -- 106
  | executionPrivateInformation2LegsMessage (message : ExecutionPrivateInformation2LegsMessage) -- 23
  | tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) -- 26
  | tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) -- 28
  | tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) -- 30
  | executionPrivateInformation1LegBuyMarketOrderMessage (message : ExecutionPrivateInformation1LegBuyMarketOrderMessage) -- 19
  | executionPrivateInformation1LegSellMarketOrderMessage (message : ExecutionPrivateInformation1LegSellMarketOrderMessage) -- 21
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .logonResponseMessage _ => 8
  | .logoutResponseMessage _ => 11
  | .heartbeatMessage _ => 48
  | .networkStatusMessage _ => 10
  | .logonMessage _ => 65
  | .rejectMessage _ => 13
  | .tradingSessionStatusMessage _ => 104
  | .newsMessage _ => 66
  | .securityListCancellationReportMessage _ => 120
  | .statisticsMessage _ => 132
  | .securityListMessage _ => 121
  | .securityListUpdateReportMessage _ => 128
  | .securityStatusMessage _ => 102
  | .orderBookClearMessage _ => 129
  | .orderMarketPreTransparencyInformationMessage _ => 3
  | .quoteMarketPreTransparencyInformationMessage _ => 7
  | .orderCancellationMarketMemberMessage _ => 1
  | .quoteCancellationMarketMemberMessage _ => 5
  | .tradeMarketPostTransparencyInformationTopofbookMessage _ => 16
  | .tradeTradeAmendmentOrCancellationMessage _ => 24
  | .tradeMarketPostTransparencyInformationFullDepthMessage _ => 17
  | .topofbookMessage _ => 130
  | .orderAndQuoteClientDataMessage _ => 111
  | .simpleNewOrderMessage _ => 68
  | .simpleNewOrderWithClientDataMessage _ => 69
  | .simpleOrderModificationMessage _ => 71
  | .simpleOrderModificationWithClientDataMessage _ => 72
  | .orderCancellationRequestMessage _ => 70
  | .newQuoteMessage _ => 83
  | .quoteModificationRequestMessage _ => 97
  | .quoteCancellationRequestMessage _ => 90
  | .massOrderquoteCancellationMessage _ => 113
  | .orderAndQuoteClientDataParametersAckNackMessage _ => 135
  | .simpleOrderStatusMessage _ => 2
  | .quoteStatusMessage _ => 6
  | .orderCancelRejectMessage _ => 57
  | .massOrderquoteCancellationCompletionMessage _ => 114
  | .massOrderquoteCancellationRejectMessage _ => 115
  | .businessMessageRejectMessage _ => 106
  | .executionPrivateInformation2LegsMessage _ => 23
  | .tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage _ => 26
  | .tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage _ => 28
  | .tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage _ => 30
  | .executionPrivateInformation1LegBuyMarketOrderMessage _ => 19
  | .executionPrivateInformation1LegSellMarketOrderMessage _ => 21

def encode : Payload → List UInt8
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .logoutResponseMessage message => LogoutResponseMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .networkStatusMessage message => NetworkStatusMessage.encode message
  | .logonMessage message => LogonMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .newsMessage message => NewsMessage.encode message
  | .securityListCancellationReportMessage message => SecurityListCancellationReportMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .securityListMessage message => SecurityListMessage.encode message
  | .securityListUpdateReportMessage message => SecurityListUpdateReportMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .orderMarketPreTransparencyInformationMessage message => OrderMarketPreTransparencyInformationMessage.encode message
  | .quoteMarketPreTransparencyInformationMessage message => QuoteMarketPreTransparencyInformationMessage.encode message
  | .orderCancellationMarketMemberMessage message => OrderCancellationMarketMemberMessage.encode message
  | .quoteCancellationMarketMemberMessage message => QuoteCancellationMarketMemberMessage.encode message
  | .tradeMarketPostTransparencyInformationTopofbookMessage message => TradeMarketPostTransparencyInformationTopofbookMessage.encode message
  | .tradeTradeAmendmentOrCancellationMessage message => TradeTradeAmendmentOrCancellationMessage.encode message
  | .tradeMarketPostTransparencyInformationFullDepthMessage message => TradeMarketPostTransparencyInformationFullDepthMessage.encode message
  | .topofbookMessage message => TopofbookMessage.encode message
  | .orderAndQuoteClientDataMessage message => OrderAndQuoteClientDataMessage.encode message
  | .simpleNewOrderMessage message => SimpleNewOrderMessage.encode message
  | .simpleNewOrderWithClientDataMessage message => SimpleNewOrderWithClientDataMessage.encode message
  | .simpleOrderModificationMessage message => SimpleOrderModificationMessage.encode message
  | .simpleOrderModificationWithClientDataMessage message => SimpleOrderModificationWithClientDataMessage.encode message
  | .orderCancellationRequestMessage message => OrderCancellationRequestMessage.encode message
  | .newQuoteMessage message => NewQuoteMessage.encode message
  | .quoteModificationRequestMessage message => QuoteModificationRequestMessage.encode message
  | .quoteCancellationRequestMessage message => QuoteCancellationRequestMessage.encode message
  | .massOrderquoteCancellationMessage message => MassOrderquoteCancellationMessage.encode message
  | .orderAndQuoteClientDataParametersAckNackMessage message => OrderAndQuoteClientDataParametersAckNackMessage.encode message
  | .simpleOrderStatusMessage message => SimpleOrderStatusMessage.encode message
  | .quoteStatusMessage message => QuoteStatusMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .massOrderquoteCancellationCompletionMessage message => MassOrderquoteCancellationCompletionMessage.encode message
  | .massOrderquoteCancellationRejectMessage message => MassOrderquoteCancellationRejectMessage.encode message
  | .businessMessageRejectMessage message => BusinessMessageRejectMessage.encode message
  | .executionPrivateInformation2LegsMessage message => ExecutionPrivateInformation2LegsMessage.encode message
  | .tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage message => TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.encode message
  | .tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage message => TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.encode message
  | .tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage message => TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.encode message
  | .executionPrivateInformation1LegBuyMarketOrderMessage message => ExecutionPrivateInformation1LegBuyMarketOrderMessage.encode message
  | .executionPrivateInformation1LegSellMarketOrderMessage message => ExecutionPrivateInformation1LegSellMarketOrderMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 976 := by
  cases message with
  | logonResponseMessage inner =>
    simp only [encode, LogonResponseMessage.encode_length]
    omega
  | logoutResponseMessage inner =>
    simp only [encode, LogoutResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | networkStatusMessage inner =>
    simp only [encode, NetworkStatusMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [encode, RejectMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [encode, NewsMessage.encode_length]
    omega
  | securityListCancellationReportMessage inner =>
    simp only [encode, SecurityListCancellationReportMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | securityListMessage inner =>
    simp only [encode, SecurityListMessage.encode_length]
    omega
  | securityListUpdateReportMessage inner =>
    simp only [encode, SecurityListUpdateReportMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | orderMarketPreTransparencyInformationMessage inner =>
    simp only [encode, OrderMarketPreTransparencyInformationMessage.encode_length]
    omega
  | quoteMarketPreTransparencyInformationMessage inner =>
    simp only [encode, QuoteMarketPreTransparencyInformationMessage.encode_length]
    omega
  | orderCancellationMarketMemberMessage inner =>
    simp only [encode, OrderCancellationMarketMemberMessage.encode_length]
    omega
  | quoteCancellationMarketMemberMessage inner =>
    simp only [encode, QuoteCancellationMarketMemberMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationTopofbookMessage inner =>
    simp only [encode, TradeMarketPostTransparencyInformationTopofbookMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellationMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationFullDepthMessage inner =>
    simp only [encode, TradeMarketPostTransparencyInformationFullDepthMessage.encode_length]
    omega
  | topofbookMessage inner =>
    simp only [encode, TopofbookMessage.encode_length]
    omega
  | orderAndQuoteClientDataMessage inner =>
    simp only [encode, OrderAndQuoteClientDataMessage.encode_length]
    omega
  | simpleNewOrderMessage inner =>
    simp only [encode, SimpleNewOrderMessage.encode_length]
    omega
  | simpleNewOrderWithClientDataMessage inner =>
    simp only [encode, SimpleNewOrderWithClientDataMessage.encode_length]
    omega
  | simpleOrderModificationMessage inner =>
    simp only [encode, SimpleOrderModificationMessage.encode_length]
    omega
  | simpleOrderModificationWithClientDataMessage inner =>
    simp only [encode, SimpleOrderModificationWithClientDataMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [encode, OrderCancellationRequestMessage.encode_length]
    omega
  | newQuoteMessage inner =>
    simp only [encode, NewQuoteMessage.encode_length]
    omega
  | quoteModificationRequestMessage inner =>
    simp only [encode, QuoteModificationRequestMessage.encode_length]
    omega
  | quoteCancellationRequestMessage inner =>
    simp only [encode, QuoteCancellationRequestMessage.encode_length]
    omega
  | massOrderquoteCancellationMessage inner =>
    simp only [encode, MassOrderquoteCancellationMessage.encode_length]
    omega
  | orderAndQuoteClientDataParametersAckNackMessage inner =>
    simp only [encode, OrderAndQuoteClientDataParametersAckNackMessage.encode_length]
    omega
  | simpleOrderStatusMessage inner =>
    simp only [encode, SimpleOrderStatusMessage.encode_length]
    omega
  | quoteStatusMessage inner =>
    simp only [encode, QuoteStatusMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [encode, OrderCancelRejectMessage.encode_length]
    omega
  | massOrderquoteCancellationCompletionMessage inner =>
    simp only [encode, MassOrderquoteCancellationCompletionMessage.encode_length]
    omega
  | massOrderquoteCancellationRejectMessage inner =>
    simp only [encode, MassOrderquoteCancellationRejectMessage.encode_length]
    omega
  | businessMessageRejectMessage inner =>
    simp only [encode, BusinessMessageRejectMessage.encode_length]
    omega
  | executionPrivateInformation2LegsMessage inner =>
    simp only [encode, ExecutionPrivateInformation2LegsMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.encode_length]
    omega
  | executionPrivateInformation1LegBuyMarketOrderMessage inner =>
    simp only [encode, ExecutionPrivateInformation1LegBuyMarketOrderMessage.encode_length]
    omega
  | executionPrivateInformation1LegSellMarketOrderMessage inner =>
    simp only [encode, ExecutionPrivateInformation1LegSellMarketOrderMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 8 then (LogonResponseMessage.decode bytes).map fun (message, rest) => (.logonResponseMessage message, rest)
  else if tag = 11 then (LogoutResponseMessage.decode bytes).map fun (message, rest) => (.logoutResponseMessage message, rest)
  else if tag = 48 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 10 then (NetworkStatusMessage.decode bytes).map fun (message, rest) => (.networkStatusMessage message, rest)
  else if tag = 65 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 13 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 104 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 66 then (NewsMessage.decode bytes).map fun (message, rest) => (.newsMessage message, rest)
  else if tag = 120 then (SecurityListCancellationReportMessage.decode bytes).map fun (message, rest) => (.securityListCancellationReportMessage message, rest)
  else if tag = 132 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 121 then (SecurityListMessage.decode bytes).map fun (message, rest) => (.securityListMessage message, rest)
  else if tag = 128 then (SecurityListUpdateReportMessage.decode bytes).map fun (message, rest) => (.securityListUpdateReportMessage message, rest)
  else if tag = 102 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 129 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 3 then (OrderMarketPreTransparencyInformationMessage.decode bytes).map fun (message, rest) => (.orderMarketPreTransparencyInformationMessage message, rest)
  else if tag = 7 then (QuoteMarketPreTransparencyInformationMessage.decode bytes).map fun (message, rest) => (.quoteMarketPreTransparencyInformationMessage message, rest)
  else if tag = 1 then (OrderCancellationMarketMemberMessage.decode bytes).map fun (message, rest) => (.orderCancellationMarketMemberMessage message, rest)
  else if tag = 5 then (QuoteCancellationMarketMemberMessage.decode bytes).map fun (message, rest) => (.quoteCancellationMarketMemberMessage message, rest)
  else if tag = 16 then (TradeMarketPostTransparencyInformationTopofbookMessage.decode bytes).map fun (message, rest) => (.tradeMarketPostTransparencyInformationTopofbookMessage message, rest)
  else if tag = 24 then (TradeTradeAmendmentOrCancellationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellationMessage message, rest)
  else if tag = 17 then (TradeMarketPostTransparencyInformationFullDepthMessage.decode bytes).map fun (message, rest) => (.tradeMarketPostTransparencyInformationFullDepthMessage message, rest)
  else if tag = 130 then (TopofbookMessage.decode bytes).map fun (message, rest) => (.topofbookMessage message, rest)
  else if tag = 111 then (OrderAndQuoteClientDataMessage.decode bytes).map fun (message, rest) => (.orderAndQuoteClientDataMessage message, rest)
  else if tag = 68 then (SimpleNewOrderMessage.decode bytes).map fun (message, rest) => (.simpleNewOrderMessage message, rest)
  else if tag = 69 then (SimpleNewOrderWithClientDataMessage.decode bytes).map fun (message, rest) => (.simpleNewOrderWithClientDataMessage message, rest)
  else if tag = 71 then (SimpleOrderModificationMessage.decode bytes).map fun (message, rest) => (.simpleOrderModificationMessage message, rest)
  else if tag = 72 then (SimpleOrderModificationWithClientDataMessage.decode bytes).map fun (message, rest) => (.simpleOrderModificationWithClientDataMessage message, rest)
  else if tag = 70 then (OrderCancellationRequestMessage.decode bytes).map fun (message, rest) => (.orderCancellationRequestMessage message, rest)
  else if tag = 83 then (NewQuoteMessage.decode bytes).map fun (message, rest) => (.newQuoteMessage message, rest)
  else if tag = 97 then (QuoteModificationRequestMessage.decode bytes).map fun (message, rest) => (.quoteModificationRequestMessage message, rest)
  else if tag = 90 then (QuoteCancellationRequestMessage.decode bytes).map fun (message, rest) => (.quoteCancellationRequestMessage message, rest)
  else if tag = 113 then (MassOrderquoteCancellationMessage.decode bytes).map fun (message, rest) => (.massOrderquoteCancellationMessage message, rest)
  else if tag = 135 then (OrderAndQuoteClientDataParametersAckNackMessage.decode bytes).map fun (message, rest) => (.orderAndQuoteClientDataParametersAckNackMessage message, rest)
  else if tag = 2 then (SimpleOrderStatusMessage.decode bytes).map fun (message, rest) => (.simpleOrderStatusMessage message, rest)
  else if tag = 6 then (QuoteStatusMessage.decode bytes).map fun (message, rest) => (.quoteStatusMessage message, rest)
  else if tag = 57 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 114 then (MassOrderquoteCancellationCompletionMessage.decode bytes).map fun (message, rest) => (.massOrderquoteCancellationCompletionMessage message, rest)
  else if tag = 115 then (MassOrderquoteCancellationRejectMessage.decode bytes).map fun (message, rest) => (.massOrderquoteCancellationRejectMessage message, rest)
  else if tag = 106 then (BusinessMessageRejectMessage.decode bytes).map fun (message, rest) => (.businessMessageRejectMessage message, rest)
  else if tag = 23 then (ExecutionPrivateInformation2LegsMessage.decode bytes).map fun (message, rest) => (.executionPrivateInformation2LegsMessage message, rest)
  else if tag = 26 then (TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage message, rest)
  else if tag = 28 then (TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage message, rest)
  else if tag = 30 then (TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage message, rest)
  else if tag = 19 then (ExecutionPrivateInformation1LegBuyMarketOrderMessage.decode bytes).map fun (message, rest) => (.executionPrivateInformation1LegBuyMarketOrderMessage message, rest)
  else if tag = 21 then (ExecutionPrivateInformation1LegSellMarketOrderMessage.decode bytes).map fun (message, rest) => (.executionPrivateInformation1LegSellMarketOrderMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | logonResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonResponseMessage.encode_length]
    omega
  | logoutResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogoutResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | networkStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NetworkStatusMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RejectMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingSessionStatusMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewsMessage.encode_length]
    omega
  | securityListCancellationReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListCancellationReportMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | securityListMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListMessage.encode_length]
    omega
  | securityListUpdateReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListUpdateReportMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityStatusMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | orderMarketPreTransparencyInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderMarketPreTransparencyInformationMessage.encode_length]
    omega
  | quoteMarketPreTransparencyInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteMarketPreTransparencyInformationMessage.encode_length]
    omega
  | orderCancellationMarketMemberMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancellationMarketMemberMessage.encode_length]
    omega
  | quoteCancellationMarketMemberMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteCancellationMarketMemberMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationTopofbookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMarketPostTransparencyInformationTopofbookMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellationMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationFullDepthMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMarketPostTransparencyInformationFullDepthMessage.encode_length]
    omega
  | topofbookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopofbookMessage.encode_length]
    omega
  | orderAndQuoteClientDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAndQuoteClientDataMessage.encode_length]
    omega
  | simpleNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleNewOrderMessage.encode_length]
    omega
  | simpleNewOrderWithClientDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleNewOrderWithClientDataMessage.encode_length]
    omega
  | simpleOrderModificationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleOrderModificationMessage.encode_length]
    omega
  | simpleOrderModificationWithClientDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleOrderModificationWithClientDataMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancellationRequestMessage.encode_length]
    omega
  | newQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewQuoteMessage.encode_length]
    omega
  | quoteModificationRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteModificationRequestMessage.encode_length]
    omega
  | quoteCancellationRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteCancellationRequestMessage.encode_length]
    omega
  | massOrderquoteCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MassOrderquoteCancellationMessage.encode_length]
    omega
  | orderAndQuoteClientDataParametersAckNackMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAndQuoteClientDataParametersAckNackMessage.encode_length]
    omega
  | simpleOrderStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleOrderStatusMessage.encode_length]
    omega
  | quoteStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteStatusMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelRejectMessage.encode_length]
    omega
  | massOrderquoteCancellationCompletionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MassOrderquoteCancellationCompletionMessage.encode_length]
    omega
  | massOrderquoteCancellationRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MassOrderquoteCancellationRejectMessage.encode_length]
    omega
  | businessMessageRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BusinessMessageRejectMessage.encode_length]
    omega
  | executionPrivateInformation2LegsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionPrivateInformation2LegsMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.encode_length]
    omega
  | executionPrivateInformation1LegBuyMarketOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionPrivateInformation1LegBuyMarketOrderMessage.encode_length]
    omega
  | executionPrivateInformation1LegSellMarketOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionPrivateInformation1LegSellMarketOrderMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.BmeBmeequitiesMarketandorderBmegateV16
