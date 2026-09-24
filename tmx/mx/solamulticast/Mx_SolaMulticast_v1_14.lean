import Omi.Wire

/-!
# TMX Group Sola Multicast v1.14

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Number Of Levels counts Market Depth Level in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Levels counts Market Depth Level in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Levels counts Market Depth Level in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Levels counts Strategy Market Depth Level in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Legs counts Strategy Instrument Leg in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Note: Number Of Bonds counts Bond Definition in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Note: Number Of Entries counts Tick Entry in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxMxSolamulticastHsvfV114

/-- Exchange Id: one byte code -/
def ExchangeId.codes : List UInt8 :=
  [0x51]

inductive ExchangeId where
  | montreal -- Montreal
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeId

def toByte : ExchangeId → UInt8
  | .montreal => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ExchangeId :=
  .montreal

def ofByte (byte : UInt8) : ExchangeId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeId) : ofByte value.toByte = value := by
  cases value with
  | montreal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExchangeId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeId

/-- Expiry Month: one byte code -/
def ExpiryMonth.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C]

inductive ExpiryMonth where
  | january -- January
  | february -- February
  | march -- March
  | april -- April
  | may -- May
  | june -- June
  | july -- July
  | august -- August
  | september -- September
  | october -- October
  | november -- November
  | december -- December
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpiryMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpiryMonth

def toByte : ExpiryMonth → UInt8
  | .january => 0x41
  | .february => 0x42
  | .march => 0x43
  | .april => 0x44
  | .may => 0x45
  | .june => 0x46
  | .july => 0x47
  | .august => 0x48
  | .september => 0x49
  | .october => 0x4A
  | .november => 0x4B
  | .december => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExpiryMonth :=
  if byte = 0x41 then .january
  else if byte = 0x42 then .february
  else if byte = 0x43 then .march
  else if byte = 0x44 then .april
  else if byte = 0x45 then .may
  else if byte = 0x46 then .june
  else if byte = 0x47 then .july
  else if byte = 0x48 then .august
  else if byte = 0x49 then .september
  else if byte = 0x4A then .october
  else if byte = 0x4B then .november
  else .december

def ofByte (byte : UInt8) : ExpiryMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpiryMonth) : ofByte value.toByte = value := by
  cases value with
  | january => decide
  | february => decide
  | march => decide
  | april => decide
  | may => decide
  | june => decide
  | july => decide
  | august => decide
  | september => decide
  | october => decide
  | november => decide
  | december => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpiryMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpiryMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpiryMonth) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExpiryMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpiryMonth

/-- Price Indicator Marker: one byte code -/
def PriceIndicatorMarker.codes : List UInt8 :=
  [0x41, 0x42, 0x20, 0x44, 0x45, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x50, 0x52, 0x53, 0x74, 0x54, 0x55, 0x56]

inductive PriceIndicatorMarker where
  | asofTrade -- Asof Trade
  | blockTrade -- Block Trade
  | transaction -- Transaction
  | crossed -- Crossed
  | efpReporting -- Efp Reporting
  | contingentTrade -- Contingent Trade
  | risklessBasisCross -- Riskless Basis Cross
  | impliedTrade -- Implied Trade
  | deltaTrade -- Delta Trade
  | committedBlock -- Committed Block
  | lateTrade -- Late Trade
  | strategyReporting -- Strategy Reporting
  | efrReporting -- Efr Reporting
  | referencePrice -- Reference Price
  | tradeCorrection -- Trade Correction
  | committed -- Committed
  | basisOnClose -- Basis On Close
  | priceVolumeAdjustment -- Price Volume Adjustment
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceIndicatorMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceIndicatorMarker

def toByte : PriceIndicatorMarker → UInt8
  | .asofTrade => 0x41
  | .blockTrade => 0x42
  | .transaction => 0x20
  | .crossed => 0x44
  | .efpReporting => 0x45
  | .contingentTrade => 0x47
  | .risklessBasisCross => 0x48
  | .impliedTrade => 0x49
  | .deltaTrade => 0x4A
  | .committedBlock => 0x4B
  | .lateTrade => 0x4C
  | .strategyReporting => 0x50
  | .efrReporting => 0x52
  | .referencePrice => 0x53
  | .tradeCorrection => 0x74
  | .committed => 0x54
  | .basisOnClose => 0x55
  | .priceVolumeAdjustment => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceIndicatorMarker :=
  if byte = 0x41 then .asofTrade
  else if byte = 0x42 then .blockTrade
  else if byte = 0x20 then .transaction
  else if byte = 0x44 then .crossed
  else if byte = 0x45 then .efpReporting
  else if byte = 0x47 then .contingentTrade
  else if byte = 0x48 then .risklessBasisCross
  else if byte = 0x49 then .impliedTrade
  else if byte = 0x4A then .deltaTrade
  else if byte = 0x4B then .committedBlock
  else if byte = 0x4C then .lateTrade
  else if byte = 0x50 then .strategyReporting
  else if byte = 0x52 then .efrReporting
  else if byte = 0x53 then .referencePrice
  else if byte = 0x74 then .tradeCorrection
  else if byte = 0x54 then .committed
  else if byte = 0x55 then .basisOnClose
  else .priceVolumeAdjustment

def ofByte (byte : UInt8) : PriceIndicatorMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceIndicatorMarker) : ofByte value.toByte = value := by
  cases value with
  | asofTrade => decide
  | blockTrade => decide
  | transaction => decide
  | crossed => decide
  | efpReporting => decide
  | contingentTrade => decide
  | risklessBasisCross => decide
  | impliedTrade => decide
  | deltaTrade => decide
  | committedBlock => decide
  | lateTrade => decide
  | strategyReporting => decide
  | efrReporting => decide
  | referencePrice => decide
  | tradeCorrection => decide
  | committed => decide
  | basisOnClose => decide
  | priceVolumeAdjustment => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceIndicatorMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceIndicatorMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceIndicatorMarker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceIndicatorMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceIndicatorMarker

/-- Call Put Code: one byte code -/
def CallPutCode.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallPutCode where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallPutCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallPutCode

def toByte : CallPutCode → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallPutCode :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallPutCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallPutCode) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallPutCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallPutCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallPutCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CallPutCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallPutCode

/-- Requested Market Side: one byte code -/
def RequestedMarketSide.codes : List UInt8 :=
  [0x42, 0x53, 0x32]

inductive RequestedMarketSide where
  | buy -- Buy
  | sell -- Sell
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ RequestedMarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RequestedMarketSide

def toByte : RequestedMarketSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .both => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RequestedMarketSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .both

def ofByte (byte : UInt8) : RequestedMarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RequestedMarketSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RequestedMarketSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RequestedMarketSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RequestedMarketSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RequestedMarketSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RequestedMarketSide

/-- Series Status: one byte code -/
def SeriesStatus.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x41, 0x43, 0x20]

inductive SeriesStatus where
  | preopening -- Preopening
  | opening -- Opening
  | continuousTrading -- Continuous Trading
  | forbidden -- Forbidden
  | interventionBeforeOpening -- Intervention Before Opening
  | haltedTrading -- Halted Trading
  | reserved -- Reserved
  | suspended -- Suspended
  | surveillanceIntervention -- Surveillance Intervention
  | endofDayInquiries -- Endof Day Inquiries
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ SeriesStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SeriesStatus

def toByte : SeriesStatus → UInt8
  | .preopening => 0x59
  | .opening => 0x4F
  | .continuousTrading => 0x54
  | .forbidden => 0x46
  | .interventionBeforeOpening => 0x45
  | .haltedTrading => 0x48
  | .reserved => 0x52
  | .suspended => 0x53
  | .surveillanceIntervention => 0x41
  | .endofDayInquiries => 0x43
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SeriesStatus :=
  if byte = 0x59 then .preopening
  else if byte = 0x4F then .opening
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x46 then .forbidden
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .haltedTrading
  else if byte = 0x52 then .reserved
  else if byte = 0x53 then .suspended
  else if byte = 0x41 then .surveillanceIntervention
  else if byte = 0x43 then .endofDayInquiries
  else .notAvailable

def ofByte (byte : UInt8) : SeriesStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SeriesStatus) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | opening => decide
  | continuousTrading => decide
  | forbidden => decide
  | interventionBeforeOpening => decide
  | haltedTrading => decide
  | reserved => decide
  | suspended => decide
  | surveillanceIntervention => decide
  | endofDayInquiries => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SeriesStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SeriesStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SeriesStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SeriesStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SeriesStatus

/-- Instrument Status Marker: one byte code -/
def InstrumentStatusMarker.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x41, 0x43, 0x20]

inductive InstrumentStatusMarker where
  | preopening -- Preopening
  | opening -- Opening
  | continuousTrading -- Continuous Trading
  | forbidden -- Forbidden
  | interventionBeforeOpening -- Intervention Before Opening
  | haltedTrading -- Halted Trading
  | reserved -- Reserved
  | suspended -- Suspended
  | surveillanceIntervention -- Surveillance Intervention
  | endofDayInquiries -- Endof Day Inquiries
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStatusMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStatusMarker

def toByte : InstrumentStatusMarker → UInt8
  | .preopening => 0x59
  | .opening => 0x4F
  | .continuousTrading => 0x54
  | .forbidden => 0x46
  | .interventionBeforeOpening => 0x45
  | .haltedTrading => 0x48
  | .reserved => 0x52
  | .suspended => 0x53
  | .surveillanceIntervention => 0x41
  | .endofDayInquiries => 0x43
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStatusMarker :=
  if byte = 0x59 then .preopening
  else if byte = 0x4F then .opening
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x46 then .forbidden
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .haltedTrading
  else if byte = 0x52 then .reserved
  else if byte = 0x53 then .suspended
  else if byte = 0x41 then .surveillanceIntervention
  else if byte = 0x43 then .endofDayInquiries
  else .notAvailable

def ofByte (byte : UInt8) : InstrumentStatusMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStatusMarker) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | opening => decide
  | continuousTrading => decide
  | forbidden => decide
  | interventionBeforeOpening => decide
  | haltedTrading => decide
  | reserved => decide
  | suspended => decide
  | surveillanceIntervention => decide
  | endofDayInquiries => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentStatusMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentStatusMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentStatusMarker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentStatusMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentStatusMarker

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x41, 0x45]

inductive OptionType where
  | american -- American
  | european -- European
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .american => 0x41
  | .european => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x41 then .american
  else .european

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Delivery Type: one byte code -/
def DeliveryType.codes : List UInt8 :=
  [0x43, 0x50]

inductive DeliveryType where
  | cash -- Cash
  | physical -- Physical
  | unlisted (byte : { byte : UInt8 // byte ∉ DeliveryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeliveryType

def toByte : DeliveryType → UInt8
  | .cash => 0x43
  | .physical => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeliveryType :=
  if byte = 0x43 then .cash
  else .physical

def ofByte (byte : UInt8) : DeliveryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeliveryType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | physical => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeliveryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeliveryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeliveryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DeliveryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeliveryType

/-- Strategy Allow Implied: one byte code -/
def StrategyAllowImplied.codes : List UInt8 :=
  [0x59, 0x4E]

inductive StrategyAllowImplied where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyAllowImplied.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyAllowImplied

def toByte : StrategyAllowImplied → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyAllowImplied :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : StrategyAllowImplied :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyAllowImplied) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyAllowImplied) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyAllowImplied × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyAllowImplied) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrategyAllowImplied) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyAllowImplied

/-- Strategy Type: one byte code -/
def StrategyType.codes : List UInt8 :=
  [0x43, 0x53, 0x56, 0x52]

inductive StrategyType where
  | classic -- Classic
  | strip -- Strip
  | coveredRegular -- Covered Regular
  | coveredReferenceFixed -- Covered Reference Fixed
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyType

def toByte : StrategyType → UInt8
  | .classic => 0x43
  | .strip => 0x53
  | .coveredRegular => 0x56
  | .coveredReferenceFixed => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyType :=
  if byte = 0x43 then .classic
  else if byte = 0x53 then .strip
  else if byte = 0x56 then .coveredRegular
  else .coveredReferenceFixed

def ofByte (byte : UInt8) : StrategyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyType) : ofByte value.toByte = value := by
  cases value with
  | classic => decide
  | strip => decide
  | coveredRegular => decide
  | coveredReferenceFixed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrategyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyType

/-- Initial Order Side: one byte code -/
def InitialOrderSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive InitialOrderSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ InitialOrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InitialOrderSide

def toByte : InitialOrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InitialOrderSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : InitialOrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InitialOrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InitialOrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InitialOrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InitialOrderSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InitialOrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InitialOrderSide

/-- Tick: one byte code -/
def Tick.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive Tick where
  | uptick -- Uptick
  | downtick -- Downtick
  | unlisted (byte : { byte : UInt8 // byte ∉ Tick.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tick

def toByte : Tick → UInt8
  | .uptick => 0x2B
  | .downtick => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tick :=
  if byte = 0x2B then .uptick
  else .downtick

def ofByte (byte : UInt8) : Tick :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tick) : ofByte value.toByte = value := by
  cases value with
  | uptick => decide
  | downtick => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tick) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tick × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tick) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tick) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tick

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x53, 0x45, 0x55, 0x43]

inductive Reason where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | instrumentNewOrUpdate -- Instrument New Or Update
  | tradeCancellation -- Trade Cancellation
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .instrumentNewOrUpdate => 0x55
  | .tradeCancellation => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x53 then .startOfDay
  else if byte = 0x45 then .endOfDay
  else if byte = 0x55 then .instrumentNewOrUpdate
  else .tradeCancellation

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | instrumentNewOrUpdate => decide
  | tradeCancellation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Reason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reason

/-- Order Side: one byte code -/
def OrderSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderSide

def toByte : OrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderSide

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x41, 0x42]

inductive OrderType where
  | initialOrder -- Initial Order
  | improvementOrder -- Improvement Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .initialOrder => 0x41
  | .improvementOrder => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x41 then .initialOrder
  else .improvementOrder

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | initialOrder => decide
  | improvementOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Option Symbol: 19 bytes -/
structure OptionSymbol where
  root : Alpha 6
  expiryMonth : ExpiryMonth
  strikePrice : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace OptionSymbol

def encode (message : OptionSymbol) : List UInt8 :=
  Alpha.encode message.root
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay)))))

def decode (bytes : List UInt8) : Option (OptionSymbol × List UInt8) := do
  let (root, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (strikePrice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ root, expiryMonth, strikePrice, strikePriceFractionIndicator, expiryYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : OptionSymbol) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ExpiryMonth.encode_length]

theorem encode_length_pos (message : OptionSymbol) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionSymbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionSymbol

/-- Option Trade Message: 60 bytes -/
structure OptionTradeMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace OptionTradeMessage

def encode (message : OptionTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, optionSymbol, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : OptionTradeMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
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
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeMessage

/-- Future Option Symbol: 20 bytes -/
structure FutureOptionSymbol where
  root : Alpha 6
  symbolMonth : Alpha 1
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePrice : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace FutureOptionSymbol

def encode (message : FutureOptionSymbol) : List UInt8 :=
  Alpha.encode message.root
    ++ (Alpha.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator))))))

def decode (bytes : List UInt8) : Option (FutureOptionSymbol × List UInt8) := do
  let (root, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← Alpha.decode 1 bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePrice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ root, symbolMonth, symbolYear, expiryDay, callPutCode, strikePrice, strikePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : FutureOptionSymbol) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length]

theorem encode_length_pos (message : FutureOptionSymbol) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionSymbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionSymbol

/-- Future Options Trade Message: 61 bytes -/
structure FutureOptionsTradeMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace FutureOptionsTradeMessage

def encode (message : FutureOptionsTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureOptionSymbol, volume, tradePrice, tradePriceFractionIndicator, priceIndicatorMarker, netChangeSign, netChange, netChangeFractionIndicator, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeMessage

/-- Future Product: 11 bytes -/
structure FutureProduct where
  root : Alpha 6
  symbolMonth : Alpha 1
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace FutureProduct

def encode (message : FutureProduct) : List UInt8 :=
  Alpha.encode message.root
    ++ (Alpha.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay)))

def decode (bytes : List UInt8) : Option (FutureProduct × List UInt8) := do
  let (root, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← Alpha.decode 1 bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ root, symbolMonth, symbolYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : FutureProduct) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FutureProduct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureProduct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureProduct

/-- Futures Trade Message: 52 bytes -/
structure FuturesTradeMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace FuturesTradeMessage

def encode (message : FuturesTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureProduct, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : FuturesTradeMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeMessage

/-- Strategy Trade Message: 72 bytes -/
structure StrategyTradeMessage where
  exchangeId : ExchangeId
  symbolStrategy : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 7
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace StrategyTradeMessage

def encode (message : StrategyTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId)))))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, symbolStrategy, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : StrategyTradeMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : StrategyTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeMessage

/-- Option Request For Quote Message: 29 bytes -/
structure OptionRequestForQuoteMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace OptionRequestForQuoteMessage

def encode (message : OptionRequestForQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (OptionRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, optionSymbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : OptionRequestForQuoteMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : OptionRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionRequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end OptionRequestForQuoteMessage

/-- Future Options Request For Quote Message: 30 bytes -/
structure FutureOptionsRequestForQuoteMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FutureOptionsRequestForQuoteMessage

def encode (message : FutureOptionsRequestForQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (FutureOptionsRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, futureOptionSymbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FutureOptionsRequestForQuoteMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FutureOptionsRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsRequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FutureOptionsRequestForQuoteMessage

/-- Future Request For Quote Message: 21 bytes -/
structure FutureRequestForQuoteMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FutureRequestForQuoteMessage

def encode (message : FutureRequestForQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (FutureRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, futureProduct, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FutureRequestForQuoteMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FutureRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureRequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FutureRequestForQuoteMessage

/-- Strategy Request For Quote Message: 40 bytes -/
structure StrategyRequestForQuoteMessage where
  exchangeId : ExchangeId
  symbolStrategy : Alpha 30
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace StrategyRequestForQuoteMessage

def encode (message : StrategyRequestForQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (StrategyRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, symbolStrategy, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : StrategyRequestForQuoteMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : StrategyRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyRequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end StrategyRequestForQuoteMessage

/-- Instrument Schedule Notice Option Message: 27 bytes -/
structure InstrumentScheduleNoticeOptionMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeOptionMessage

def encode (message : InstrumentScheduleNoticeOptionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeOptionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, optionSymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeOptionMessage

/-- Instrument Schedule Notice Futures Option Message: 28 bytes -/
structure InstrumentScheduleNoticeFuturesOptionMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFuturesOptionMessage

def encode (message : InstrumentScheduleNoticeFuturesOptionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFuturesOptionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureOptionSymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFuturesOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFuturesOptionMessage

/-- Instrument Schedule Notice Future Message: 19 bytes -/
structure InstrumentScheduleNoticeFutureMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFutureMessage

def encode (message : InstrumentScheduleNoticeFutureMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFutureMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureProduct, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFutureMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFutureMessage

/-- Instrument Schedule Notice Strategy Message: 38 bytes -/
structure InstrumentScheduleNoticeStrategyMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeStrategyMessage

def encode (message : InstrumentScheduleNoticeStrategyMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeStrategyMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, strategySymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, SeriesStatus.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeStrategyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeStrategyMessage

/-- Option Quote Message: 47 bytes -/
structure OptionQuoteMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace OptionQuoteMessage

def encode (message : OptionQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))))

def decode (bytes : List UInt8) : Option (OptionQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, optionSymbol, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : OptionQuoteMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : OptionQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
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
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end OptionQuoteMessage

/-- Future Options Quote Message: 48 bytes -/
structure FutureOptionsQuoteMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace FutureOptionsQuoteMessage

def encode (message : FutureOptionsQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, futureOptionSymbol, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : FutureOptionsQuoteMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
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
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end FutureOptionsQuoteMessage

/-- Futures Quote Message: 39 bytes -/
structure FuturesQuoteMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace FuturesQuoteMessage

def encode (message : FuturesQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))))

def decode (bytes : List UInt8) : Option (FuturesQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, futureProduct, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : FuturesQuoteMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : FuturesQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end FuturesQuoteMessage

/-- Strategy Quote Message: 60 bytes -/
structure StrategyQuoteMessage where
  exchangeId : ExchangeId
  symbolStrategy : Alpha 30
  bidPriceSign : Alpha 1
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSign : Alpha 1
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace StrategyQuoteMessage

def encode (message : StrategyQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))))))

def decode (bytes : List UInt8) : Option (StrategyQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, symbolStrategy, bidPriceSign, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceSign, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : StrategyQuoteMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : StrategyQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end StrategyQuoteMessage

/-- Market Depth Level: 31 bytes -/
structure MarketDepthLevel where
  levelOfMarketDepth : Alpha 1
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace MarketDepthLevel

def encode (message : MarketDepthLevel) : List UInt8 :=
  Alpha.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (MarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : MarketDepthLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketDepthLevel

/-- Option Market Depth Message -/
structure OptionMarketDepthMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  instrumentStatusMarker : InstrumentStatusMarker
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace OptionMarketDepthMessage

def encode (message : OptionMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevels bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, optionSymbol, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionMarketDepthMessage) : (encode message).length ≤ 301 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, OptionSymbol.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end OptionMarketDepthMessage

/-- Future Options Market Depth Message -/
structure FutureOptionsMarketDepthMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  instrumentStatusMarker : InstrumentStatusMarker
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthMessage

def encode (message : FutureOptionsMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevels bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, futureOptionSymbol, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : FutureOptionsMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FutureOptionsMarketDepthMessage) : (encode message).length ≤ 302 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, FutureOptionSymbol.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end FutureOptionsMarketDepthMessage

/-- Futures Market Depth Message -/
structure FuturesMarketDepthMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  instrumentStatusMarker : InstrumentStatusMarker
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace FuturesMarketDepthMessage

def encode (message : FuturesMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevels bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, futureProduct, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : FuturesMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FuturesMarketDepthMessage) : (encode message).length ≤ 293 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, FutureProduct.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : FuturesMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end FuturesMarketDepthMessage

/-- Strategy Market Depth Level: 33 bytes -/
structure StrategyMarketDepthLevel where
  levelOfMarketDepth : Alpha 1
  bidPriceSign : Alpha 1
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceSign : Alpha 1
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace StrategyMarketDepthLevel

def encode (message : StrategyMarketDepthLevel) : List UInt8 :=
  Alpha.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← Alpha.decode 1 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceSign, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceSign, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : StrategyMarketDepthLevel) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategyMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyMarketDepthLevel

/-- Strategy Market Depth Message -/
structure StrategyMarketDepthMessage where
  exchangeId : ExchangeId
  symbolStrategy : Alpha 30
  instrumentStatusMarker : InstrumentStatusMarker
  strategyMarketDepthLevel : Digited 1 StrategyMarketDepthLevel
  deriving DecidableEq, Repr

namespace StrategyMarketDepthMessage

def encode (message : StrategyMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.strategyMarketDepthLevel.val.length
    ++ (encodeMany StrategyMarketDepthLevel.encode message.strategyMarketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (strategyMarketDepthLevel_, bytes) ← decodeMany StrategyMarketDepthLevel.decode numberOfLevels bytes
  if fits_strategyMarketDepthLevel : strategyMarketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, symbolStrategy, instrumentStatusMarker, strategyMarketDepthLevel := ⟨strategyMarketDepthLevel_, fits_strategyMarketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyMarketDepthMessage) : (encode message).length ≤ 330 := by
  have bound_strategyMarketDepthLevel := message.strategyMarketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const StrategyMarketDepthLevel.encode 33 StrategyMarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyMarketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyMarketDepthLevel.encode StrategyMarketDepthLevel.decode StrategyMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyMarketDepthLevel.length_lt]
  rfl

end StrategyMarketDepthMessage

/-- Option Trade Cancellation Message: 51 bytes -/
structure OptionTradeCancellationMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace OptionTradeCancellationMessage

def encode (message : OptionTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId)))))))

def decode (bytes : List UInt8) : Option (OptionTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, optionSymbol, volume, tradePrice, tradePriceFractionIndicator, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : OptionTradeCancellationMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeCancellationMessage

/-- Future Options Trade Cancellation Message: 52 bytes -/
structure FutureOptionsTradeCancellationMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  volume : Alpha 8
  price : Alpha 7
  priceFractionIndicator : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace FutureOptionsTradeCancellationMessage

def encode (message : FutureOptionsTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.priceFractionIndicator
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId)))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 7 bytes
  let (priceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureOptionSymbol, volume, price, priceFractionIndicator, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeCancellationMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeCancellationMessage

/-- Future Trade Cancellation Message: 43 bytes -/
structure FutureTradeCancellationMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace FutureTradeCancellationMessage

def encode (message : FutureTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId)))))))

def decode (bytes : List UInt8) : Option (FutureTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureProduct, volume, tradePrice, tradePriceFractionIndicator, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : FutureTradeCancellationMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FutureTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureTradeCancellationMessage

/-- Strategy Trade Cancellation Message: 62 bytes -/
structure StrategyTradeCancellationMessage where
  exchangeId : ExchangeId
  symbolStrategy : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 7
  tradePriceFractionIndicator : Alpha 1
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace StrategyTradeCancellationMessage

def encode (message : StrategyTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId)))))))

def decode (bytes : List UInt8) : Option (StrategyTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, symbolStrategy, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : StrategyTradeCancellationMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeCancellationMessage

/-- Option Instrument Keys Message: 146 bytes -/
structure OptionInstrumentKeysMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceInstrument : Alpha 7
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 7
  tickIncrementFractionIndicator : Alpha 1
  optionType : OptionType
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  optionMarker : Alpha 2
  underlyingSymbolRoot : Alpha 12
  contractSize : Alpha 8
  tickValue : Alpha 7
  tickValueFractionIndicator : Alpha 1
  currency : Alpha 3
  deliveryType : DeliveryType
  lastTradingDatetime : Alpha 14
  deriving DecidableEq, Repr

namespace OptionInstrumentKeysMessage

def encode (message : OptionInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceInstrument
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRoot
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (Alpha.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType
    ++ (Alpha.encode message.lastTradingDatetime)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRoot, bytes) ← Alpha.decode 12 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 7 bytes
  let (tickValueFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (lastTradingDatetime, bytes) ← Alpha.decode 14 bytes
  pure ({ exchangeId, optionSymbol, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPriceInstrument, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, optionType, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, optionMarker, underlyingSymbolRoot, contractSize, tickValue, tickValueFractionIndicator, currency, deliveryType, lastTradingDatetime }, bytes)

@[simp] theorem encode_length (message : OptionInstrumentKeysMessage) : (encode message).length = 146 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, OptionType.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : OptionInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionInstrumentKeysMessage

/-- Future Options Instrument Keys Message: 147 bytes -/
structure FutureOptionsInstrumentKeysMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  expiryDate : Alpha 6
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceInstrument : Alpha 7
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 7
  tickIncrementFractionIndicator : Alpha 1
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValue : Alpha 7
  tickValueFractionIndicator : Alpha 1
  currency : Alpha 3
  deliveryType : DeliveryType
  underlyingRootSymbol : Alpha 6
  underlyingSymbolMonth : Alpha 1
  underlyingSymbolYear : Alpha 2
  lastTradingDatetime : Alpha 14
  deriving DecidableEq, Repr

namespace FutureOptionsInstrumentKeysMessage

def encode (message : FutureOptionsInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceInstrument
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (Alpha.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType
    ++ (Alpha.encode message.underlyingRootSymbol
    ++ (Alpha.encode message.underlyingSymbolMonth
    ++ (Alpha.encode message.underlyingSymbolYear
    ++ (Alpha.encode message.lastTradingDatetime))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FutureOptionsInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 6 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 7 bytes
  let (tickValueFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (underlyingRootSymbol, bytes) ← Alpha.decode 6 bytes
  let (underlyingSymbolMonth, bytes) ← Alpha.decode 1 bytes
  let (underlyingSymbolYear, bytes) ← Alpha.decode 2 bytes
  let (lastTradingDatetime, bytes) ← Alpha.decode 14 bytes
  pure ({ exchangeId, futureOptionSymbol, expiryDate, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPriceInstrument, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValue, tickValueFractionIndicator, currency, deliveryType, underlyingRootSymbol, underlyingSymbolMonth, underlyingSymbolYear, lastTradingDatetime }, bytes)

@[simp] theorem encode_length (message : FutureOptionsInstrumentKeysMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : FutureOptionsInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FutureOptionsInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsInstrumentKeysMessage

/-- Underlying Instrument Keys Message: 39 bytes -/
structure UnderlyingInstrumentKeysMessage where
  exchangeId : ExchangeId
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  marketFlowIndicator : Alpha 2
  deriving DecidableEq, Repr

namespace UnderlyingInstrumentKeysMessage

def encode (message : UnderlyingInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.marketFlowIndicator))))

def decode (bytes : List UInt8) : Option (UnderlyingInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  pure ({ exchangeId, groupInstrument, instrument, instrumentExternalCode, marketFlowIndicator }, bytes)

@[simp] theorem encode_length (message : UnderlyingInstrumentKeysMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingInstrumentKeysMessage

/-- Associated Product: 11 bytes -/
structure AssociatedProduct where
  root : Alpha 6
  symbolMonth : Alpha 1
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace AssociatedProduct

def encode (message : AssociatedProduct) : List UInt8 :=
  Alpha.encode message.root
    ++ (Alpha.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay)))

def decode (bytes : List UInt8) : Option (AssociatedProduct × List UInt8) := do
  let (root, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← Alpha.decode 1 bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ root, symbolMonth, symbolYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : AssociatedProduct) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : AssociatedProduct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AssociatedProduct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AssociatedProduct

/-- Futures Instrument Keys Message: 149 bytes -/
structure FuturesInstrumentKeysMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  expiryDate : Alpha 6
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceInstrument : Alpha 7
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 7
  tickIncrementFractionIndicator : Alpha 1
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValue : Alpha 7
  tickValueFractionIndicator : Alpha 1
  currency : Alpha 3
  underlyingSymbol : Alpha 12
  deliveryType : DeliveryType
  associatedProduct : AssociatedProduct
  lastTradingDatetime : Alpha 14
  deriving DecidableEq, Repr

namespace FuturesInstrumentKeysMessage

def encode (message : FuturesInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceInstrument
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (Alpha.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.underlyingSymbol
    ++ (DeliveryType.encode message.deliveryType
    ++ (AssociatedProduct.encode message.associatedProduct
    ++ (Alpha.encode message.lastTradingDatetime))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 6 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 7 bytes
  let (tickValueFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 12 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (associatedProduct, bytes) ← AssociatedProduct.decode bytes
  let (lastTradingDatetime, bytes) ← Alpha.decode 14 bytes
  pure ({ exchangeId, futureProduct, expiryDate, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPriceInstrument, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValue, tickValueFractionIndicator, currency, underlyingSymbol, deliveryType, associatedProduct, lastTradingDatetime }, bytes)

@[simp] theorem encode_length (message : FuturesInstrumentKeysMessage) : (encode message).length = 149 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, DeliveryType.encode_length, AssociatedProduct.encode_length]

theorem encode_length_pos (message : FuturesInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AssociatedProduct.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesInstrumentKeysMessage

/-- Strategy Instrument Leg: 19 bytes -/
structure StrategyInstrumentLeg where
  legGroupInstrument : Alpha 2
  legInstrument : Alpha 4
  legRatioOrDelta : Alpha 4
  legRatioOrDeltaFractionIndicator : Alpha 1
  legPrice : Alpha 7
  legPriceFractionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace StrategyInstrumentLeg

def encode (message : StrategyInstrumentLeg) : List UInt8 :=
  Alpha.encode message.legGroupInstrument
    ++ (Alpha.encode message.legInstrument
    ++ (Alpha.encode message.legRatioOrDelta
    ++ (Alpha.encode message.legRatioOrDeltaFractionIndicator
    ++ (Alpha.encode message.legPrice
    ++ (Alpha.encode message.legPriceFractionIndicator)))))

def decode (bytes : List UInt8) : Option (StrategyInstrumentLeg × List UInt8) := do
  let (legGroupInstrument, bytes) ← Alpha.decode 2 bytes
  let (legInstrument, bytes) ← Alpha.decode 4 bytes
  let (legRatioOrDelta, bytes) ← Alpha.decode 4 bytes
  let (legRatioOrDeltaFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (legPrice, bytes) ← Alpha.decode 7 bytes
  let (legPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ legGroupInstrument, legInstrument, legRatioOrDelta, legRatioOrDeltaFractionIndicator, legPrice, legPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : StrategyInstrumentLeg) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategyInstrumentLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyInstrumentLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyInstrumentLeg

/-- Strategy Instrument Keys Message -/
structure StrategyInstrumentKeysMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  expiryYear : Alpha 2
  expiryMonth : ExpiryMonth
  expiryDay : Alpha 2
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceStrategy : Alpha 7
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 7
  tickIncrementFractionIndicator : Alpha 1
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  strategyAllowImplied : StrategyAllowImplied
  strategyCode : Alpha 2
  strategyType : StrategyType
  lastTradingDatetime : Alpha 14
  variableLegsStrategyCode : Alpha 2
  strategyInstrumentLeg : Digited 2 StrategyInstrumentLeg
  deriving DecidableEq, Repr

namespace StrategyInstrumentKeysMessage

def encode (message : StrategyInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.expiryYear
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceStrategy
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (StrategyAllowImplied.encode message.strategyAllowImplied
    ++ (Alpha.encode message.strategyCode
    ++ (StrategyType.encode message.strategyType
    ++ (Alpha.encode message.lastTradingDatetime
    ++ (Alpha.encode message.variableLegsStrategyCode
    ++ (encodeDigits 2 message.strategyInstrumentLeg.val.length
    ++ (encodeMany StrategyInstrumentLeg.encode message.strategyInstrumentLeg.val)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategyInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceStrategy, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (strategyAllowImplied, bytes) ← StrategyAllowImplied.decode bytes
  let (strategyCode, bytes) ← Alpha.decode 2 bytes
  let (strategyType, bytes) ← StrategyType.decode bytes
  let (lastTradingDatetime, bytes) ← Alpha.decode 14 bytes
  let (variableLegsStrategyCode, bytes) ← Alpha.decode 2 bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (strategyInstrumentLeg_, bytes) ← decodeMany StrategyInstrumentLeg.decode numberOfLegs bytes
  if fits_strategyInstrumentLeg : strategyInstrumentLeg_.length < 10 ^ 2 then
    pure ({ exchangeId, strategySymbol, expiryYear, expiryMonth, expiryDay, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPriceStrategy, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, strategyAllowImplied, strategyCode, strategyType, lastTradingDatetime, variableLegsStrategyCode, strategyInstrumentLeg := ⟨strategyInstrumentLeg_, fits_strategyInstrumentLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyInstrumentKeysMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyInstrumentKeysMessage) : (encode message).length ≤ 2013 := by
  have bound_strategyInstrumentLeg := message.strategyInstrumentLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrategyAllowImplied.encode_length, StrategyType.encode_length, encodeDigits_length, encodeMany_length_const StrategyInstrumentLeg.encode 19 StrategyInstrumentLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
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
  rw [List.append_assoc, StrategyAllowImplied.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyInstrumentLeg.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyInstrumentLeg.encode StrategyInstrumentLeg.decode StrategyInstrumentLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyInstrumentLeg.length_lt]
  rfl

end StrategyInstrumentKeysMessage

/-- Option Auction Beginning Message: 83 bytes -/
structure OptionAuctionBeginningMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  auctionId : Alpha 6
  initialOrderSide : InitialOrderSide
  initialOrderQuantity : Alpha 8
  initialOrderPrice : Alpha 7
  initialOrderPriceFractionIndicator : Alpha 1
  auctionExpiryTimestamp : Alpha 20
  auctionDuration : Alpha 12
  initialQuantityAssured : Alpha 8
  deriving DecidableEq, Repr

namespace OptionAuctionBeginningMessage

def encode (message : OptionAuctionBeginningMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.auctionId
    ++ (InitialOrderSide.encode message.initialOrderSide
    ++ (Alpha.encode message.initialOrderQuantity
    ++ (Alpha.encode message.initialOrderPrice
    ++ (Alpha.encode message.initialOrderPriceFractionIndicator
    ++ (Alpha.encode message.auctionExpiryTimestamp
    ++ (Alpha.encode message.auctionDuration
    ++ (Alpha.encode message.initialQuantityAssured)))))))))

def decode (bytes : List UInt8) : Option (OptionAuctionBeginningMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (initialOrderSide, bytes) ← InitialOrderSide.decode bytes
  let (initialOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (initialOrderPrice, bytes) ← Alpha.decode 7 bytes
  let (initialOrderPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (auctionExpiryTimestamp, bytes) ← Alpha.decode 20 bytes
  let (auctionDuration, bytes) ← Alpha.decode 12 bytes
  let (initialQuantityAssured, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, optionSymbol, auctionId, initialOrderSide, initialOrderQuantity, initialOrderPrice, initialOrderPriceFractionIndicator, auctionExpiryTimestamp, auctionDuration, initialQuantityAssured }, bytes)

@[simp] theorem encode_length (message : OptionAuctionBeginningMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, InitialOrderSide.encode_length]

theorem encode_length_pos (message : OptionAuctionBeginningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionAuctionBeginningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderSide.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionAuctionBeginningMessage

/-- Strategy Auction Beginning Message: 94 bytes -/
structure StrategyAuctionBeginningMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  auctionId : Alpha 6
  initialOrderSide : InitialOrderSide
  initialOrderQuantity : Alpha 8
  initialOrderPrice : Alpha 7
  initialOrderPriceFractionIndicator : Alpha 1
  auctionExpiryTimestamp : Alpha 20
  auctionDuration : Alpha 12
  initialQuantityAssured : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyAuctionBeginningMessage

def encode (message : StrategyAuctionBeginningMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.auctionId
    ++ (InitialOrderSide.encode message.initialOrderSide
    ++ (Alpha.encode message.initialOrderQuantity
    ++ (Alpha.encode message.initialOrderPrice
    ++ (Alpha.encode message.initialOrderPriceFractionIndicator
    ++ (Alpha.encode message.auctionExpiryTimestamp
    ++ (Alpha.encode message.auctionDuration
    ++ (Alpha.encode message.initialQuantityAssured)))))))))

def decode (bytes : List UInt8) : Option (StrategyAuctionBeginningMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (initialOrderSide, bytes) ← InitialOrderSide.decode bytes
  let (initialOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (initialOrderPrice, bytes) ← Alpha.decode 7 bytes
  let (initialOrderPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (auctionExpiryTimestamp, bytes) ← Alpha.decode 20 bytes
  let (auctionDuration, bytes) ← Alpha.decode 12 bytes
  let (initialQuantityAssured, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, strategySymbol, auctionId, initialOrderSide, initialOrderQuantity, initialOrderPrice, initialOrderPriceFractionIndicator, auctionExpiryTimestamp, auctionDuration, initialQuantityAssured }, bytes)

@[simp] theorem encode_length (message : StrategyAuctionBeginningMessage) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, InitialOrderSide.encode_length]

theorem encode_length_pos (message : StrategyAuctionBeginningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyAuctionBeginningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderSide.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyAuctionBeginningMessage

/-- Option Summary Message: 128 bytes -/
structure OptionSummaryMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  bidPriceSummary : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSummary : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPrice : Alpha 7
  lastPriceFractionIndicator : Alpha 1
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  tick : Tick
  volume : Alpha 8
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  openPrice : Alpha 7
  openPriceFractionIndicator : Alpha 1
  highPrice : Alpha 7
  highPriceFractionIndicator : Alpha 1
  lowPrice : Alpha 7
  lowPriceFractionIndicator : Alpha 1
  optionMarker : Alpha 2
  closingPrice : Alpha 7
  closingPriceFractionIndicator : Alpha 1
  previousClosingPrice : Alpha 7
  previousClosingPriceFractionIndicator : Alpha 1
  reason : Reason
  deriving DecidableEq, Repr

namespace OptionSummaryMessage

def encode (message : OptionSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.closingPriceFractionIndicator
    ++ (Alpha.encode message.previousClosingPrice
    ++ (Alpha.encode message.previousClosingPriceFractionIndicator
    ++ (Reason.encode message.reason))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OptionSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 7 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (closingPrice, bytes) ← Alpha.decode 7 bytes
  let (closingPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (previousClosingPrice, bytes) ← Alpha.decode 7 bytes
  let (previousClosingPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, optionSymbol, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openInterest, openInterestDate, tick, volume, netChangeSign, netChange, netChangeFractionIndicator, openPrice, openPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, optionMarker, closingPrice, closingPriceFractionIndicator, previousClosingPrice, previousClosingPriceFractionIndicator, reason }, bytes)

@[simp] theorem encode_length (message : OptionSummaryMessage) : (encode message).length = 128 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, Tick.encode_length, Reason.encode_length]

theorem encode_length_pos (message : OptionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OptionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end OptionSummaryMessage

/-- Future Options Summary Message: 127 bytes -/
structure FutureOptionsSummaryMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  bidPriceSummary : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSummary : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPrice : Alpha 7
  lastPriceFractionIndicator : Alpha 1
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  tick : Tick
  volume : Alpha 8
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  openingPrice : Alpha 7
  openingPriceFractionIndicator : Alpha 1
  highPrice : Alpha 7
  highPriceFractionIndicator : Alpha 1
  lowPrice : Alpha 7
  lowPriceFractionIndicator : Alpha 1
  settlementPrice : Alpha 7
  settlementPriceFractionIndicator : Alpha 1
  previousSettlementPrice : Alpha 7
  previousSettlementPriceFractionIndicator : Alpha 1
  reason : Reason
  deriving DecidableEq, Repr

namespace FutureOptionsSummaryMessage

def encode (message : FutureOptionsSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.openingPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.settlementPrice
    ++ (Alpha.encode message.settlementPriceFractionIndicator
    ++ (Alpha.encode message.previousSettlementPrice
    ++ (Alpha.encode message.previousSettlementPriceFractionIndicator
    ++ (Reason.encode message.reason)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FutureOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openingPrice, bytes) ← Alpha.decode 7 bytes
  let (openingPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (settlementPrice, bytes) ← Alpha.decode 7 bytes
  let (settlementPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (previousSettlementPrice, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, futureOptionSymbol, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openInterest, openInterestDate, tick, volume, netChangeSign, netChange, netChangeFractionIndicator, openingPrice, openingPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, settlementPrice, settlementPriceFractionIndicator, previousSettlementPrice, previousSettlementPriceFractionIndicator, reason }, bytes)

@[simp] theorem encode_length (message : FutureOptionsSummaryMessage) : (encode message).length = 127 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, Tick.encode_length, Reason.encode_length]

theorem encode_length_pos (message : FutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
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
  rw [Reason.decode_encode, some_bind]
  rfl

end FutureOptionsSummaryMessage

/-- Futures Summary Message: 125 bytes -/
structure FuturesSummaryMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  bidPriceSummary : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSummary : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPrice : Alpha 7
  lastPriceFractionIndicator : Alpha 1
  openPrice : Alpha 7
  openPriceFractionIndicator : Alpha 1
  highPrice : Alpha 7
  highPriceFractionIndicator : Alpha 1
  lowPrice : Alpha 7
  lowPriceFractionIndicator : Alpha 1
  settlementPrice : Alpha 7
  settlementPriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  volume : Alpha 8
  previousSettlement : Alpha 7
  previousSettlementFractionIndicator : Alpha 1
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  reason : Reason
  externalPriceAtSource : Alpha 7
  externalPriceFractionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace FuturesSummaryMessage

def encode (message : FuturesSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.settlementPrice
    ++ (Alpha.encode message.settlementPriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.previousSettlement
    ++ (Alpha.encode message.previousSettlementFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Reason.encode message.reason
    ++ (Alpha.encode message.externalPriceAtSource
    ++ (Alpha.encode message.externalPriceFractionIndicator))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FuturesSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 7 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (settlementPrice, bytes) ← Alpha.decode 7 bytes
  let (settlementPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (previousSettlement, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (reason, bytes) ← Reason.decode bytes
  let (externalPriceAtSource, bytes) ← Alpha.decode 7 bytes
  let (externalPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, futureProduct, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openPrice, openPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, settlementPrice, settlementPriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, volume, previousSettlement, previousSettlementFractionIndicator, openInterest, openInterestDate, reason, externalPriceAtSource, externalPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : FuturesSummaryMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, Reason.encode_length]

theorem encode_length_pos (message : FuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Reason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesSummaryMessage

/-- Strategy Summary Message: 113 bytes -/
structure StrategySummaryMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  bidPriceSign : Alpha 1
  bidPriceSummary : Alpha 7
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSign : Alpha 1
  askPriceSummary : Alpha 7
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPriceSign : Alpha 1
  lastPrice : Alpha 7
  lastPriceFractionIndicator : Alpha 1
  openPriceSign : Alpha 1
  openPrice : Alpha 7
  openPriceFractionIndicator : Alpha 1
  highPriceSign : Alpha 1
  highPrice : Alpha 7
  highPriceFractionIndicator : Alpha 1
  lowPriceSign : Alpha 1
  lowPrice : Alpha 7
  lowPriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  volume : Alpha 8
  reason : Reason
  deriving DecidableEq, Repr

namespace StrategySummaryMessage

def encode (message : StrategySummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPriceSign
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openPriceSign
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPriceSign
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPriceSign
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Reason.encode message.reason))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (StrategySummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceSign, bytes) ← Alpha.decode 1 bytes
  let (lastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPriceSign, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 7 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPriceSign, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPriceSign, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, strategySymbol, bidPriceSign, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSign, askPriceSummary, askPriceFractionIndicator, askSize, lastPriceSign, lastPrice, lastPriceFractionIndicator, openPriceSign, openPrice, openPriceFractionIndicator, highPriceSign, highPrice, highPriceFractionIndicator, lowPriceSign, lowPrice, lowPriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, volume, reason }, bytes)

@[simp] theorem encode_length (message : StrategySummaryMessage) : (encode message).length = 113 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, Reason.encode_length]

theorem encode_length_pos (message : StrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : StrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end StrategySummaryMessage

/-- Option Initial And Improvement Order Message: 60 bytes -/
structure OptionInitialAndImprovementOrderMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  auctionId : Alpha 6
  orderSide : OrderSide
  orderQuantity : Alpha 8
  orderPrice : Alpha 7
  orderPriceFractionIndicator : Alpha 1
  orderType : OrderType
  orderId : Alpha 8
  previousOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace OptionInitialAndImprovementOrderMessage

def encode (message : OptionInitialAndImprovementOrderMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.auctionId
    ++ (OrderSide.encode message.orderSide
    ++ (Alpha.encode message.orderQuantity
    ++ (Alpha.encode message.orderPrice
    ++ (Alpha.encode message.orderPriceFractionIndicator
    ++ (OrderType.encode message.orderType
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.previousOrderId)))))))))

def decode (bytes : List UInt8) : Option (OptionInitialAndImprovementOrderMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (orderQuantity, bytes) ← Alpha.decode 8 bytes
  let (orderPrice, bytes) ← Alpha.decode 7 bytes
  let (orderPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (previousOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, optionSymbol, auctionId, orderSide, orderQuantity, orderPrice, orderPriceFractionIndicator, orderType, orderId, previousOrderId }, bytes)

@[simp] theorem encode_length (message : OptionInitialAndImprovementOrderMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, OrderSide.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : OptionInitialAndImprovementOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInitialAndImprovementOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionInitialAndImprovementOrderMessage

/-- Strategy Initial And Improvement Order Message: 71 bytes -/
structure StrategyInitialAndImprovementOrderMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  auctionId : Alpha 6
  orderSide : OrderSide
  orderQuantity : Alpha 8
  orderPrice : Alpha 7
  orderPriceFractionIndicator : Alpha 1
  orderType : OrderType
  orderId : Alpha 8
  previousOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyInitialAndImprovementOrderMessage

def encode (message : StrategyInitialAndImprovementOrderMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.auctionId
    ++ (OrderSide.encode message.orderSide
    ++ (Alpha.encode message.orderQuantity
    ++ (Alpha.encode message.orderPrice
    ++ (Alpha.encode message.orderPriceFractionIndicator
    ++ (OrderType.encode message.orderType
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.previousOrderId)))))))))

def decode (bytes : List UInt8) : Option (StrategyInitialAndImprovementOrderMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (orderQuantity, bytes) ← Alpha.decode 8 bytes
  let (orderPrice, bytes) ← Alpha.decode 7 bytes
  let (orderPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (previousOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, strategySymbol, auctionId, orderSide, orderQuantity, orderPrice, orderPriceFractionIndicator, orderType, orderId, previousOrderId }, bytes)

@[simp] theorem encode_length (message : StrategyInitialAndImprovementOrderMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, OrderSide.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : StrategyInitialAndImprovementOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyInitialAndImprovementOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyInitialAndImprovementOrderMessage

/-- Beginning Of Options Summary Message: 1 bytes -/
structure BeginningOfOptionsSummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfOptionsSummaryMessage

def encode (message : BeginningOfOptionsSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfOptionsSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfOptionsSummaryMessage

/-- Beginning Of Future Options Summary Message: 1 bytes -/
structure BeginningOfFutureOptionsSummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfFutureOptionsSummaryMessage

def encode (message : BeginningOfFutureOptionsSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfFutureOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfFutureOptionsSummaryMessage

/-- Beginning Of Futures Summary Message: 1 bytes -/
structure BeginningOfFuturesSummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfFuturesSummaryMessage

def encode (message : BeginningOfFuturesSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfFuturesSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFuturesSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfFuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfFuturesSummaryMessage

/-- Beginning Of Strategy Summary Message: 1 bytes -/
structure BeginningOfStrategySummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfStrategySummaryMessage

def encode (message : BeginningOfStrategySummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfStrategySummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfStrategySummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfStrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfStrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfStrategySummaryMessage

/-- Option Auction Ending Message: 26 bytes -/
structure OptionAuctionEndingMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace OptionAuctionEndingMessage

def encode (message : OptionAuctionEndingMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.auctionId))

def decode (bytes : List UInt8) : Option (OptionAuctionEndingMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, optionSymbol, auctionId }, bytes)

@[simp] theorem encode_length (message : OptionAuctionEndingMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionAuctionEndingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionAuctionEndingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionAuctionEndingMessage

/-- Strategy Auction Ending Message: 37 bytes -/
structure StrategyAuctionEndingMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace StrategyAuctionEndingMessage

def encode (message : StrategyAuctionEndingMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.auctionId))

def decode (bytes : List UInt8) : Option (StrategyAuctionEndingMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, strategySymbol, auctionId }, bytes)

@[simp] theorem encode_length (message : StrategyAuctionEndingMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyAuctionEndingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyAuctionEndingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyAuctionEndingMessage

/-- Futures Trade Correction Message: 46 bytes -/
structure FuturesTradeCorrectionMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCorrectionMessage

def encode (message : FuturesTradeCorrectionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, futureProduct, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCorrectionMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCorrectionMessage

/-- Group Status Message: 8 bytes -/
structure GroupStatusMessage where
  exchangeId : ExchangeId
  root : Alpha 6
  groupStatus : Alpha 1
  deriving DecidableEq, Repr

namespace GroupStatusMessage

def encode (message : GroupStatusMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.root
    ++ (Alpha.encode message.groupStatus))

def decode (bytes : List UInt8) : Option (GroupStatusMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (root, bytes) ← Alpha.decode 6 bytes
  let (groupStatus, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, root, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : GroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GroupStatusMessage

/-- Group Status Strategies Message: 4 bytes -/
structure GroupStatusStrategiesMessage where
  exchangeId : ExchangeId
  groupInstrument : Alpha 2
  groupStatus : Alpha 1
  deriving DecidableEq, Repr

namespace GroupStatusStrategiesMessage

def encode (message : GroupStatusStrategiesMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.groupStatus))

def decode (bytes : List UInt8) : Option (GroupStatusStrategiesMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (groupStatus, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, groupInstrument, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusStrategiesMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : GroupStatusStrategiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusStrategiesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GroupStatusStrategiesMessage

/-- Bond Definition: 32 bytes -/
structure BondDefinition where
  maturityDate : Alpha 8
  coupon : Alpha 7
  couponFractionIndicator : Alpha 1
  outstandingBondValue : Alpha 8
  conversionFactor : Alpha 7
  conversionFactorFractionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace BondDefinition

def encode (message : BondDefinition) : List UInt8 :=
  Alpha.encode message.maturityDate
    ++ (Alpha.encode message.coupon
    ++ (Alpha.encode message.couponFractionIndicator
    ++ (Alpha.encode message.outstandingBondValue
    ++ (Alpha.encode message.conversionFactor
    ++ (Alpha.encode message.conversionFactorFractionIndicator)))))

def decode (bytes : List UInt8) : Option (BondDefinition × List UInt8) := do
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (coupon, bytes) ← Alpha.decode 7 bytes
  let (couponFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (outstandingBondValue, bytes) ← Alpha.decode 8 bytes
  let (conversionFactor, bytes) ← Alpha.decode 7 bytes
  let (conversionFactorFractionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ maturityDate, coupon, couponFractionIndicator, outstandingBondValue, conversionFactor, conversionFactorFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BondDefinition) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BondDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BondDefinition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end BondDefinition

/-- Future Deliverables Message -/
structure FutureDeliverablesMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  bondDefinition : Digited 2 BondDefinition
  deriving DecidableEq, Repr

namespace FutureDeliverablesMessage

def encode (message : FutureDeliverablesMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (encodeDigits 2 message.bondDefinition.val.length
    ++ (encodeMany BondDefinition.encode message.bondDefinition.val)))

def decode (bytes : List UInt8) : Option (FutureDeliverablesMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (numberOfBonds, bytes) ← decodeDigits 2 bytes
  let (bondDefinition_, bytes) ← decodeMany BondDefinition.decode numberOfBonds bytes
  if fits_bondDefinition : bondDefinition_.length < 10 ^ 2 then
    pure ({ exchangeId, futureProduct, bondDefinition := ⟨bondDefinition_, fits_bondDefinition⟩ }, bytes)
  else none

theorem encode_length_pos (message : FutureDeliverablesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FutureDeliverablesMessage) : (encode message).length ≤ 3182 := by
  have bound_bondDefinition := message.bondDefinition.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, FutureProduct.encode_length, encodeDigits_length, encodeMany_length_const BondDefinition.encode 32 BondDefinition.encode_length]
  omega

@[simp] theorem decode_encode (message : FutureDeliverablesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bondDefinition.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BondDefinition.encode BondDefinition.decode BondDefinition.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bondDefinition.length_lt]
  rfl

end FutureDeliverablesMessage

/-- Regular Text Bulletin: 80 bytes -/
structure RegularTextBulletin where
  regularBulletinContents : Alpha 79
  continueMarker : Alpha 1
  deriving DecidableEq, Repr

namespace RegularTextBulletin

def encode (message : RegularTextBulletin) : List UInt8 :=
  Alpha.encode message.regularBulletinContents
    ++ (Alpha.encode message.continueMarker)

def decode (bytes : List UInt8) : Option (RegularTextBulletin × List UInt8) := do
  let (regularBulletinContents, bytes) ← Alpha.decode 79 bytes
  let (continueMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ regularBulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : RegularTextBulletin) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : RegularTextBulletin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegularTextBulletin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RegularTextBulletin

/-- Special Text Bulletin: 80 bytes -/
structure SpecialTextBulletin where
  symbolBulletin : Alpha 30
  specialBulletinContents : Alpha 49
  continueMarker : Alpha 1
  deriving DecidableEq, Repr

namespace SpecialTextBulletin

def encode (message : SpecialTextBulletin) : List UInt8 :=
  Alpha.encode message.symbolBulletin
    ++ (Alpha.encode message.specialBulletinContents
    ++ (Alpha.encode message.continueMarker))

def decode (bytes : List UInt8) : Option (SpecialTextBulletin × List UInt8) := do
  let (symbolBulletin, bytes) ← Alpha.decode 30 bytes
  let (specialBulletinContents, bytes) ← Alpha.decode 49 bytes
  let (continueMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolBulletin, specialBulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : SpecialTextBulletin) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SpecialTextBulletin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialTextBulletin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpecialTextBulletin

/-- Any Bulletin, selected by Bulletin Type -/
inductive Bulletin where
  | regularTextBulletin (message : RegularTextBulletin) -- "1" 0x31
  | specialTextBulletin (message : SpecialTextBulletin) -- "2" 0x32
  deriving DecidableEq, Repr

namespace Bulletin

/-- The Bulletin Type each message is sent under -/
def tag : Bulletin → BitVec 8
  | .regularTextBulletin _ => 49
  | .specialTextBulletin _ => 50

def encode : Bulletin → List UInt8
  | .regularTextBulletin message => RegularTextBulletin.encode message
  | .specialTextBulletin message => SpecialTextBulletin.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Bulletin) : (encode message).length ≤ 80 := by
  cases message with
  | regularTextBulletin inner =>
    simp only [encode, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [encode, SpecialTextBulletin.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Bulletin × List UInt8) :=
  if tag = 49 then (RegularTextBulletin.decode bytes).map fun (message, rest) => (.regularTextBulletin message, rest)
  else if tag = 50 then (SpecialTextBulletin.decode bytes).map fun (message, rest) => (.specialTextBulletin message, rest)
  else none

@[simp] theorem decode_encode (message : Bulletin) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Bulletin

/-- Bulletins Message -/
structure BulletinsMessage where
  reserved : Alpha 1
  bulletin : Bulletin
  deriving DecidableEq, Repr

namespace BulletinsMessage

def encode (message : BulletinsMessage) : List UInt8 :=
  Alpha.encode message.reserved
    ++ (encodeUInt 1 (Bulletin.tag message.bulletin)
    ++ (Bulletin.encode message.bulletin))

def decode (bytes : List UInt8) : Option (BulletinsMessage × List UInt8) := do
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (bulletinType, bytes) ← decodeUInt 1 bytes
  let (bulletin, bytes) ← Bulletin.decode bulletinType bytes
  pure ({ reserved, bulletin }, bytes)

theorem encode_length_pos (message : BulletinsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulletinsMessage) : (encode message).length ≤ 82 := by
  unfold encode
  cases message.bulletin with
  | regularTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SpecialTextBulletin.encode_length]
    omega

@[simp] theorem decode_encode (message : BulletinsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Bulletin.decode_encode, some_bind]
  rfl

end BulletinsMessage

/-- End Of Sales Message: 7 bytes -/
structure EndOfSalesMessage where
  reserved : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfSalesMessage

def encode (message : EndOfSalesMessage) : List UInt8 :=
  Alpha.encode message.reserved
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (EndOfSalesMessage × List UInt8) := do
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ reserved, time }, bytes)

@[simp] theorem encode_length (message : EndOfSalesMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfSalesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSalesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfSalesMessage

/-- Tick Entry: 16 bytes -/
structure TickEntry where
  minPrice : Alpha 7
  minPriceFractionIndicator : Alpha 1
  tickPrice : Alpha 7
  tickPriceFractionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace TickEntry

def encode (message : TickEntry) : List UInt8 :=
  Alpha.encode message.minPrice
    ++ (Alpha.encode message.minPriceFractionIndicator
    ++ (Alpha.encode message.tickPrice
    ++ (Alpha.encode message.tickPriceFractionIndicator)))

def decode (bytes : List UInt8) : Option (TickEntry × List UInt8) := do
  let (minPrice, bytes) ← Alpha.decode 7 bytes
  let (minPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickPrice, bytes) ← Alpha.decode 7 bytes
  let (tickPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ minPrice, minPriceFractionIndicator, tickPrice, tickPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickEntry) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TickEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TickEntry

/-- Tick Table Message -/
structure TickTableMessage where
  exchangeId : ExchangeId
  tickTableName : Alpha 50
  tickTableShortName : Alpha 2
  tickEntry : Digited 2 TickEntry
  deriving DecidableEq, Repr

namespace TickTableMessage

def encode (message : TickTableMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.tickTableName
    ++ (Alpha.encode message.tickTableShortName
    ++ (encodeDigits 2 message.tickEntry.val.length
    ++ (encodeMany TickEntry.encode message.tickEntry.val))))

def decode (bytes : List UInt8) : Option (TickTableMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (tickTableName, bytes) ← Alpha.decode 50 bytes
  let (tickTableShortName, bytes) ← Alpha.decode 2 bytes
  let (numberOfEntries, bytes) ← decodeDigits 2 bytes
  let (tickEntry_, bytes) ← decodeMany TickEntry.decode numberOfEntries bytes
  if fits_tickEntry : tickEntry_.length < 10 ^ 2 then
    pure ({ exchangeId, tickTableName, tickTableShortName, tickEntry := ⟨tickEntry_, fits_tickEntry⟩ }, bytes)
  else none

theorem encode_length_pos (message : TickTableMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TickTableMessage) : (encode message).length ≤ 1639 := by
  have bound_tickEntry := message.tickEntry.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const TickEntry.encode 16 TickEntry.encode_length]
  omega

@[simp] theorem decode_encode (message : TickTableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.tickEntry.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany TickEntry.encode TickEntry.decode TickEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tickEntry.length_lt]
  rfl

end TickTableMessage

/-- End Of Transmission Message: 7 bytes -/
structure EndOfTransmissionMessage where
  exchangeId : ExchangeId
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmissionMessage

def encode (message : EndOfTransmissionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (EndOfTransmissionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, time }, bytes)

@[simp] theorem encode_length (message : EndOfTransmissionMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmissionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmissionMessage

/-- Circuit Assurance Message: 6 bytes -/
structure CircuitAssuranceMessage where
  time : Alpha 6
  deriving DecidableEq, Repr

namespace CircuitAssuranceMessage

def encode (message : CircuitAssuranceMessage) : List UInt8 :=
  Alpha.encode message.time

def decode (bytes : List UInt8) : Option (CircuitAssuranceMessage × List UInt8) := do
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ time }, bytes)

@[simp] theorem encode_length (message : CircuitAssuranceMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CircuitAssuranceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CircuitAssuranceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CircuitAssuranceMessage

/-- Start Of Day Message: 9 bytes -/
structure StartOfDayMessage where
  exchangeId : ExchangeId
  businessDate : Alpha 8
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.businessDate)

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, businessDate }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StartOfDayMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | optionTradeMessage (message : OptionTradeMessage) -- "C " 0x4320
  | futureOptionsTradeMessage (message : FutureOptionsTradeMessage) -- "CB" 0x4342
  | futuresTradeMessage (message : FuturesTradeMessage) -- "CF" 0x4346
  | strategyTradeMessage (message : StrategyTradeMessage) -- "CS" 0x4353
  | optionRequestForQuoteMessage (message : OptionRequestForQuoteMessage) -- "D " 0x4420
  | futureOptionsRequestForQuoteMessage (message : FutureOptionsRequestForQuoteMessage) -- "DB" 0x4442
  | futureRequestForQuoteMessage (message : FutureRequestForQuoteMessage) -- "DF" 0x4446
  | strategyRequestForQuoteMessage (message : StrategyRequestForQuoteMessage) -- "DS" 0x4453
  | instrumentScheduleNoticeOptionMessage (message : InstrumentScheduleNoticeOptionMessage) -- "E " 0x4520
  | instrumentScheduleNoticeFuturesOptionMessage (message : InstrumentScheduleNoticeFuturesOptionMessage) -- "EB" 0x4542
  | instrumentScheduleNoticeFutureMessage (message : InstrumentScheduleNoticeFutureMessage) -- "EF" 0x4546
  | instrumentScheduleNoticeStrategyMessage (message : InstrumentScheduleNoticeStrategyMessage) -- "ES" 0x4553
  | optionQuoteMessage (message : OptionQuoteMessage) -- "F " 0x4620
  | futureOptionsQuoteMessage (message : FutureOptionsQuoteMessage) -- "FB" 0x4642
  | futuresQuoteMessage (message : FuturesQuoteMessage) -- "FF" 0x4646
  | strategyQuoteMessage (message : StrategyQuoteMessage) -- "FS" 0x4653
  | optionMarketDepthMessage (message : OptionMarketDepthMessage) -- "H " 0x4820
  | futureOptionsMarketDepthMessage (message : FutureOptionsMarketDepthMessage) -- "HB" 0x4842
  | futuresMarketDepthMessage (message : FuturesMarketDepthMessage) -- "HF" 0x4846
  | strategyMarketDepthMessage (message : StrategyMarketDepthMessage) -- "HS" 0x4853
  | optionTradeCancellationMessage (message : OptionTradeCancellationMessage) -- "I " 0x4920
  | futureOptionsTradeCancellationMessage (message : FutureOptionsTradeCancellationMessage) -- "IB" 0x4942
  | futureTradeCancellationMessage (message : FutureTradeCancellationMessage) -- "IF" 0x4946
  | strategyTradeCancellationMessage (message : StrategyTradeCancellationMessage) -- "IS" 0x4953
  | optionInstrumentKeysMessage (message : OptionInstrumentKeysMessage) -- "J " 0x4A20
  | futureOptionsInstrumentKeysMessage (message : FutureOptionsInstrumentKeysMessage) -- "JB" 0x4A42
  | underlyingInstrumentKeysMessage (message : UnderlyingInstrumentKeysMessage) -- "JE" 0x4A45
  | futuresInstrumentKeysMessage (message : FuturesInstrumentKeysMessage) -- "JF" 0x4A46
  | strategyInstrumentKeysMessage (message : StrategyInstrumentKeysMessage) -- "JS" 0x4A53
  | optionAuctionBeginningMessage (message : OptionAuctionBeginningMessage) -- "M " 0x4D20
  | strategyAuctionBeginningMessage (message : StrategyAuctionBeginningMessage) -- "MS" 0x4D53
  | optionSummaryMessage (message : OptionSummaryMessage) -- "N " 0x4E20
  | futureOptionsSummaryMessage (message : FutureOptionsSummaryMessage) -- "NB" 0x4E42
  | futuresSummaryMessage (message : FuturesSummaryMessage) -- "NF" 0x4E46
  | strategySummaryMessage (message : StrategySummaryMessage) -- "NS" 0x4E53
  | optionInitialAndImprovementOrderMessage (message : OptionInitialAndImprovementOrderMessage) -- "O " 0x4F20
  | strategyInitialAndImprovementOrderMessage (message : StrategyInitialAndImprovementOrderMessage) -- "OS" 0x4F53
  | beginningOfOptionsSummaryMessage (message : BeginningOfOptionsSummaryMessage) -- "Q " 0x5120
  | beginningOfFutureOptionsSummaryMessage (message : BeginningOfFutureOptionsSummaryMessage) -- "QB" 0x5142
  | beginningOfFuturesSummaryMessage (message : BeginningOfFuturesSummaryMessage) -- "QF" 0x5146
  | beginningOfStrategySummaryMessage (message : BeginningOfStrategySummaryMessage) -- "QS" 0x5153
  | optionAuctionEndingMessage (message : OptionAuctionEndingMessage) -- "T " 0x5420
  | strategyAuctionEndingMessage (message : StrategyAuctionEndingMessage) -- "TS" 0x5453
  | futuresTradeCorrectionMessage (message : FuturesTradeCorrectionMessage) -- "XF" 0x5846
  | groupStatusMessage (message : GroupStatusMessage) -- "GR" 0x4752
  | groupStatusStrategiesMessage (message : GroupStatusStrategiesMessage) -- "GS" 0x4753
  | futureDeliverablesMessage (message : FutureDeliverablesMessage) -- "KF" 0x4B46
  | bulletinsMessage (message : BulletinsMessage) -- "L " 0x4C20
  | endOfSalesMessage (message : EndOfSalesMessage) -- "S " 0x5320
  | tickTableMessage (message : TickTableMessage) -- "TT" 0x5454
  | endOfTransmissionMessage (message : EndOfTransmissionMessage) -- "U " 0x5520
  | circuitAssuranceMessage (message : CircuitAssuranceMessage) -- "V " 0x5620
  | startOfDayMessage (message : StartOfDayMessage) -- "SD" 0x5344
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .optionTradeMessage _ => 17184
  | .futureOptionsTradeMessage _ => 17218
  | .futuresTradeMessage _ => 17222
  | .strategyTradeMessage _ => 17235
  | .optionRequestForQuoteMessage _ => 17440
  | .futureOptionsRequestForQuoteMessage _ => 17474
  | .futureRequestForQuoteMessage _ => 17478
  | .strategyRequestForQuoteMessage _ => 17491
  | .instrumentScheduleNoticeOptionMessage _ => 17696
  | .instrumentScheduleNoticeFuturesOptionMessage _ => 17730
  | .instrumentScheduleNoticeFutureMessage _ => 17734
  | .instrumentScheduleNoticeStrategyMessage _ => 17747
  | .optionQuoteMessage _ => 17952
  | .futureOptionsQuoteMessage _ => 17986
  | .futuresQuoteMessage _ => 17990
  | .strategyQuoteMessage _ => 18003
  | .optionMarketDepthMessage _ => 18464
  | .futureOptionsMarketDepthMessage _ => 18498
  | .futuresMarketDepthMessage _ => 18502
  | .strategyMarketDepthMessage _ => 18515
  | .optionTradeCancellationMessage _ => 18720
  | .futureOptionsTradeCancellationMessage _ => 18754
  | .futureTradeCancellationMessage _ => 18758
  | .strategyTradeCancellationMessage _ => 18771
  | .optionInstrumentKeysMessage _ => 18976
  | .futureOptionsInstrumentKeysMessage _ => 19010
  | .underlyingInstrumentKeysMessage _ => 19013
  | .futuresInstrumentKeysMessage _ => 19014
  | .strategyInstrumentKeysMessage _ => 19027
  | .optionAuctionBeginningMessage _ => 19744
  | .strategyAuctionBeginningMessage _ => 19795
  | .optionSummaryMessage _ => 20000
  | .futureOptionsSummaryMessage _ => 20034
  | .futuresSummaryMessage _ => 20038
  | .strategySummaryMessage _ => 20051
  | .optionInitialAndImprovementOrderMessage _ => 20256
  | .strategyInitialAndImprovementOrderMessage _ => 20307
  | .beginningOfOptionsSummaryMessage _ => 20768
  | .beginningOfFutureOptionsSummaryMessage _ => 20802
  | .beginningOfFuturesSummaryMessage _ => 20806
  | .beginningOfStrategySummaryMessage _ => 20819
  | .optionAuctionEndingMessage _ => 21536
  | .strategyAuctionEndingMessage _ => 21587
  | .futuresTradeCorrectionMessage _ => 22598
  | .groupStatusMessage _ => 18258
  | .groupStatusStrategiesMessage _ => 18259
  | .futureDeliverablesMessage _ => 19270
  | .bulletinsMessage _ => 19488
  | .endOfSalesMessage _ => 21280
  | .tickTableMessage _ => 21588
  | .endOfTransmissionMessage _ => 21792
  | .circuitAssuranceMessage _ => 22048
  | .startOfDayMessage _ => 21316

def encode : MessageBody → List UInt8
  | .optionTradeMessage message => OptionTradeMessage.encode message
  | .futureOptionsTradeMessage message => FutureOptionsTradeMessage.encode message
  | .futuresTradeMessage message => FuturesTradeMessage.encode message
  | .strategyTradeMessage message => StrategyTradeMessage.encode message
  | .optionRequestForQuoteMessage message => OptionRequestForQuoteMessage.encode message
  | .futureOptionsRequestForQuoteMessage message => FutureOptionsRequestForQuoteMessage.encode message
  | .futureRequestForQuoteMessage message => FutureRequestForQuoteMessage.encode message
  | .strategyRequestForQuoteMessage message => StrategyRequestForQuoteMessage.encode message
  | .instrumentScheduleNoticeOptionMessage message => InstrumentScheduleNoticeOptionMessage.encode message
  | .instrumentScheduleNoticeFuturesOptionMessage message => InstrumentScheduleNoticeFuturesOptionMessage.encode message
  | .instrumentScheduleNoticeFutureMessage message => InstrumentScheduleNoticeFutureMessage.encode message
  | .instrumentScheduleNoticeStrategyMessage message => InstrumentScheduleNoticeStrategyMessage.encode message
  | .optionQuoteMessage message => OptionQuoteMessage.encode message
  | .futureOptionsQuoteMessage message => FutureOptionsQuoteMessage.encode message
  | .futuresQuoteMessage message => FuturesQuoteMessage.encode message
  | .strategyQuoteMessage message => StrategyQuoteMessage.encode message
  | .optionMarketDepthMessage message => OptionMarketDepthMessage.encode message
  | .futureOptionsMarketDepthMessage message => FutureOptionsMarketDepthMessage.encode message
  | .futuresMarketDepthMessage message => FuturesMarketDepthMessage.encode message
  | .strategyMarketDepthMessage message => StrategyMarketDepthMessage.encode message
  | .optionTradeCancellationMessage message => OptionTradeCancellationMessage.encode message
  | .futureOptionsTradeCancellationMessage message => FutureOptionsTradeCancellationMessage.encode message
  | .futureTradeCancellationMessage message => FutureTradeCancellationMessage.encode message
  | .strategyTradeCancellationMessage message => StrategyTradeCancellationMessage.encode message
  | .optionInstrumentKeysMessage message => OptionInstrumentKeysMessage.encode message
  | .futureOptionsInstrumentKeysMessage message => FutureOptionsInstrumentKeysMessage.encode message
  | .underlyingInstrumentKeysMessage message => UnderlyingInstrumentKeysMessage.encode message
  | .futuresInstrumentKeysMessage message => FuturesInstrumentKeysMessage.encode message
  | .strategyInstrumentKeysMessage message => StrategyInstrumentKeysMessage.encode message
  | .optionAuctionBeginningMessage message => OptionAuctionBeginningMessage.encode message
  | .strategyAuctionBeginningMessage message => StrategyAuctionBeginningMessage.encode message
  | .optionSummaryMessage message => OptionSummaryMessage.encode message
  | .futureOptionsSummaryMessage message => FutureOptionsSummaryMessage.encode message
  | .futuresSummaryMessage message => FuturesSummaryMessage.encode message
  | .strategySummaryMessage message => StrategySummaryMessage.encode message
  | .optionInitialAndImprovementOrderMessage message => OptionInitialAndImprovementOrderMessage.encode message
  | .strategyInitialAndImprovementOrderMessage message => StrategyInitialAndImprovementOrderMessage.encode message
  | .beginningOfOptionsSummaryMessage message => BeginningOfOptionsSummaryMessage.encode message
  | .beginningOfFutureOptionsSummaryMessage message => BeginningOfFutureOptionsSummaryMessage.encode message
  | .beginningOfFuturesSummaryMessage message => BeginningOfFuturesSummaryMessage.encode message
  | .beginningOfStrategySummaryMessage message => BeginningOfStrategySummaryMessage.encode message
  | .optionAuctionEndingMessage message => OptionAuctionEndingMessage.encode message
  | .strategyAuctionEndingMessage message => StrategyAuctionEndingMessage.encode message
  | .futuresTradeCorrectionMessage message => FuturesTradeCorrectionMessage.encode message
  | .groupStatusMessage message => GroupStatusMessage.encode message
  | .groupStatusStrategiesMessage message => GroupStatusStrategiesMessage.encode message
  | .futureDeliverablesMessage message => FutureDeliverablesMessage.encode message
  | .bulletinsMessage message => BulletinsMessage.encode message
  | .endOfSalesMessage message => EndOfSalesMessage.encode message
  | .tickTableMessage message => TickTableMessage.encode message
  | .endOfTransmissionMessage message => EndOfTransmissionMessage.encode message
  | .circuitAssuranceMessage message => CircuitAssuranceMessage.encode message
  | .startOfDayMessage message => StartOfDayMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 3182 := by
  cases message with
  | optionTradeMessage inner =>
    simp only [encode, OptionTradeMessage.encode_length]
    omega
  | futureOptionsTradeMessage inner =>
    simp only [encode, FutureOptionsTradeMessage.encode_length]
    omega
  | futuresTradeMessage inner =>
    simp only [encode, FuturesTradeMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [encode, StrategyTradeMessage.encode_length]
    omega
  | optionRequestForQuoteMessage inner =>
    simp only [encode, OptionRequestForQuoteMessage.encode_length]
    omega
  | futureOptionsRequestForQuoteMessage inner =>
    simp only [encode, FutureOptionsRequestForQuoteMessage.encode_length]
    omega
  | futureRequestForQuoteMessage inner =>
    simp only [encode, FutureRequestForQuoteMessage.encode_length]
    omega
  | strategyRequestForQuoteMessage inner =>
    simp only [encode, StrategyRequestForQuoteMessage.encode_length]
    omega
  | instrumentScheduleNoticeOptionMessage inner =>
    simp only [encode, InstrumentScheduleNoticeOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFuturesOptionMessage inner =>
    simp only [encode, InstrumentScheduleNoticeFuturesOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFutureMessage inner =>
    simp only [encode, InstrumentScheduleNoticeFutureMessage.encode_length]
    omega
  | instrumentScheduleNoticeStrategyMessage inner =>
    simp only [encode, InstrumentScheduleNoticeStrategyMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [encode, OptionQuoteMessage.encode_length]
    omega
  | futureOptionsQuoteMessage inner =>
    simp only [encode, FutureOptionsQuoteMessage.encode_length]
    omega
  | futuresQuoteMessage inner =>
    simp only [encode, FuturesQuoteMessage.encode_length]
    omega
  | strategyQuoteMessage inner =>
    simp only [encode, StrategyQuoteMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | futureOptionsMarketDepthMessage inner =>
    have bound_inner := FutureOptionsMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | futuresMarketDepthMessage inner =>
    have bound_inner := FuturesMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | strategyMarketDepthMessage inner =>
    have bound_inner := StrategyMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [encode, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [encode, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futureTradeCancellationMessage inner =>
    simp only [encode, FutureTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [encode, StrategyTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [encode, OptionInstrumentKeysMessage.encode_length]
    omega
  | futureOptionsInstrumentKeysMessage inner =>
    simp only [encode, FutureOptionsInstrumentKeysMessage.encode_length]
    omega
  | underlyingInstrumentKeysMessage inner =>
    simp only [encode, UnderlyingInstrumentKeysMessage.encode_length]
    omega
  | futuresInstrumentKeysMessage inner =>
    simp only [encode, FuturesInstrumentKeysMessage.encode_length]
    omega
  | strategyInstrumentKeysMessage inner =>
    have bound_inner := StrategyInstrumentKeysMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionAuctionBeginningMessage inner =>
    simp only [encode, OptionAuctionBeginningMessage.encode_length]
    omega
  | strategyAuctionBeginningMessage inner =>
    simp only [encode, StrategyAuctionBeginningMessage.encode_length]
    omega
  | optionSummaryMessage inner =>
    simp only [encode, OptionSummaryMessage.encode_length]
    omega
  | futureOptionsSummaryMessage inner =>
    simp only [encode, FutureOptionsSummaryMessage.encode_length]
    omega
  | futuresSummaryMessage inner =>
    simp only [encode, FuturesSummaryMessage.encode_length]
    omega
  | strategySummaryMessage inner =>
    simp only [encode, StrategySummaryMessage.encode_length]
    omega
  | optionInitialAndImprovementOrderMessage inner =>
    simp only [encode, OptionInitialAndImprovementOrderMessage.encode_length]
    omega
  | strategyInitialAndImprovementOrderMessage inner =>
    simp only [encode, StrategyInitialAndImprovementOrderMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFutureOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfFutureOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFuturesSummaryMessage inner =>
    simp only [encode, BeginningOfFuturesSummaryMessage.encode_length]
    omega
  | beginningOfStrategySummaryMessage inner =>
    simp only [encode, BeginningOfStrategySummaryMessage.encode_length]
    omega
  | optionAuctionEndingMessage inner =>
    simp only [encode, OptionAuctionEndingMessage.encode_length]
    omega
  | strategyAuctionEndingMessage inner =>
    simp only [encode, StrategyAuctionEndingMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [encode, FuturesTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [encode, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [encode, GroupStatusStrategiesMessage.encode_length]
    omega
  | futureDeliverablesMessage inner =>
    have bound_inner := FutureDeliverablesMessage.encode_length_le inner
    simp only [encode]
    omega
  | bulletinsMessage inner =>
    have bound_inner := BulletinsMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfSalesMessage inner =>
    simp only [encode, EndOfSalesMessage.encode_length]
    omega
  | tickTableMessage inner =>
    have bound_inner := TickTableMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfTransmissionMessage inner =>
    simp only [encode, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [encode, CircuitAssuranceMessage.encode_length]
    omega
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 17184 then (OptionTradeMessage.decode bytes).map fun (message, rest) => (.optionTradeMessage message, rest)
  else if tag = 17218 then (FutureOptionsTradeMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeMessage message, rest)
  else if tag = 17222 then (FuturesTradeMessage.decode bytes).map fun (message, rest) => (.futuresTradeMessage message, rest)
  else if tag = 17235 then (StrategyTradeMessage.decode bytes).map fun (message, rest) => (.strategyTradeMessage message, rest)
  else if tag = 17440 then (OptionRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.optionRequestForQuoteMessage message, rest)
  else if tag = 17474 then (FutureOptionsRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.futureOptionsRequestForQuoteMessage message, rest)
  else if tag = 17478 then (FutureRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.futureRequestForQuoteMessage message, rest)
  else if tag = 17491 then (StrategyRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.strategyRequestForQuoteMessage message, rest)
  else if tag = 17696 then (InstrumentScheduleNoticeOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeOptionMessage message, rest)
  else if tag = 17730 then (InstrumentScheduleNoticeFuturesOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFuturesOptionMessage message, rest)
  else if tag = 17734 then (InstrumentScheduleNoticeFutureMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFutureMessage message, rest)
  else if tag = 17747 then (InstrumentScheduleNoticeStrategyMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeStrategyMessage message, rest)
  else if tag = 17952 then (OptionQuoteMessage.decode bytes).map fun (message, rest) => (.optionQuoteMessage message, rest)
  else if tag = 17986 then (FutureOptionsQuoteMessage.decode bytes).map fun (message, rest) => (.futureOptionsQuoteMessage message, rest)
  else if tag = 17990 then (FuturesQuoteMessage.decode bytes).map fun (message, rest) => (.futuresQuoteMessage message, rest)
  else if tag = 18003 then (StrategyQuoteMessage.decode bytes).map fun (message, rest) => (.strategyQuoteMessage message, rest)
  else if tag = 18464 then (OptionMarketDepthMessage.decode bytes).map fun (message, rest) => (.optionMarketDepthMessage message, rest)
  else if tag = 18498 then (FutureOptionsMarketDepthMessage.decode bytes).map fun (message, rest) => (.futureOptionsMarketDepthMessage message, rest)
  else if tag = 18502 then (FuturesMarketDepthMessage.decode bytes).map fun (message, rest) => (.futuresMarketDepthMessage message, rest)
  else if tag = 18515 then (StrategyMarketDepthMessage.decode bytes).map fun (message, rest) => (.strategyMarketDepthMessage message, rest)
  else if tag = 18720 then (OptionTradeCancellationMessage.decode bytes).map fun (message, rest) => (.optionTradeCancellationMessage message, rest)
  else if tag = 18754 then (FutureOptionsTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeCancellationMessage message, rest)
  else if tag = 18758 then (FutureTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futureTradeCancellationMessage message, rest)
  else if tag = 18771 then (StrategyTradeCancellationMessage.decode bytes).map fun (message, rest) => (.strategyTradeCancellationMessage message, rest)
  else if tag = 18976 then (OptionInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.optionInstrumentKeysMessage message, rest)
  else if tag = 19010 then (FutureOptionsInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futureOptionsInstrumentKeysMessage message, rest)
  else if tag = 19013 then (UnderlyingInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.underlyingInstrumentKeysMessage message, rest)
  else if tag = 19014 then (FuturesInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futuresInstrumentKeysMessage message, rest)
  else if tag = 19027 then (StrategyInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.strategyInstrumentKeysMessage message, rest)
  else if tag = 19744 then (OptionAuctionBeginningMessage.decode bytes).map fun (message, rest) => (.optionAuctionBeginningMessage message, rest)
  else if tag = 19795 then (StrategyAuctionBeginningMessage.decode bytes).map fun (message, rest) => (.strategyAuctionBeginningMessage message, rest)
  else if tag = 20000 then (OptionSummaryMessage.decode bytes).map fun (message, rest) => (.optionSummaryMessage message, rest)
  else if tag = 20034 then (FutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.futureOptionsSummaryMessage message, rest)
  else if tag = 20038 then (FuturesSummaryMessage.decode bytes).map fun (message, rest) => (.futuresSummaryMessage message, rest)
  else if tag = 20051 then (StrategySummaryMessage.decode bytes).map fun (message, rest) => (.strategySummaryMessage message, rest)
  else if tag = 20256 then (OptionInitialAndImprovementOrderMessage.decode bytes).map fun (message, rest) => (.optionInitialAndImprovementOrderMessage message, rest)
  else if tag = 20307 then (StrategyInitialAndImprovementOrderMessage.decode bytes).map fun (message, rest) => (.strategyInitialAndImprovementOrderMessage message, rest)
  else if tag = 20768 then (BeginningOfOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfOptionsSummaryMessage message, rest)
  else if tag = 20802 then (BeginningOfFutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFutureOptionsSummaryMessage message, rest)
  else if tag = 20806 then (BeginningOfFuturesSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFuturesSummaryMessage message, rest)
  else if tag = 20819 then (BeginningOfStrategySummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfStrategySummaryMessage message, rest)
  else if tag = 21536 then (OptionAuctionEndingMessage.decode bytes).map fun (message, rest) => (.optionAuctionEndingMessage message, rest)
  else if tag = 21587 then (StrategyAuctionEndingMessage.decode bytes).map fun (message, rest) => (.strategyAuctionEndingMessage message, rest)
  else if tag = 22598 then (FuturesTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.futuresTradeCorrectionMessage message, rest)
  else if tag = 18258 then (GroupStatusMessage.decode bytes).map fun (message, rest) => (.groupStatusMessage message, rest)
  else if tag = 18259 then (GroupStatusStrategiesMessage.decode bytes).map fun (message, rest) => (.groupStatusStrategiesMessage message, rest)
  else if tag = 19270 then (FutureDeliverablesMessage.decode bytes).map fun (message, rest) => (.futureDeliverablesMessage message, rest)
  else if tag = 19488 then (BulletinsMessage.decode bytes).map fun (message, rest) => (.bulletinsMessage message, rest)
  else if tag = 21280 then (EndOfSalesMessage.decode bytes).map fun (message, rest) => (.endOfSalesMessage message, rest)
  else if tag = 21588 then (TickTableMessage.decode bytes).map fun (message, rest) => (.tickTableMessage message, rest)
  else if tag = 21792 then (EndOfTransmissionMessage.decode bytes).map fun (message, rest) => (.endOfTransmissionMessage message, rest)
  else if tag = 22048 then (CircuitAssuranceMessage.decode bytes).map fun (message, rest) => (.circuitAssuranceMessage message, rest)
  else if tag = 21316 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Packet -/
structure Packet where
  hsvfStx : BitVec 8
  sequenceNumber : Alpha 10
  messageTimestamp : Alpha 20
  messageBody : MessageBody
  hsvfEtx : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.hsvfStx
    ++ (Alpha.encode message.sequenceNumber
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (Alpha.encode message.messageTimestamp
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.hsvfEtx)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (hsvfStx, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 10 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageTimestamp, bytes) ← Alpha.decode 20 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (hsvfEtx, bytes) ← decodeUInt 1 bytes
  pure ({ hsvfStx, sequenceNumber, messageTimestamp, messageBody, hsvfEtx }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 3216 := by
  unfold encode
  cases message.messageBody with
  | optionTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeMessage.encode_length]
    omega
  | futureOptionsTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeMessage.encode_length]
    omega
  | futuresTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeMessage.encode_length]
    omega
  | optionRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionRequestForQuoteMessage.encode_length]
    omega
  | futureOptionsRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsRequestForQuoteMessage.encode_length]
    omega
  | futureRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureRequestForQuoteMessage.encode_length]
    omega
  | strategyRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyRequestForQuoteMessage.encode_length]
    omega
  | instrumentScheduleNoticeOptionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFuturesOptionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeFuturesOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFutureMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeFutureMessage.encode_length]
    omega
  | instrumentScheduleNoticeStrategyMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeStrategyMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionQuoteMessage.encode_length]
    omega
  | futureOptionsQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsQuoteMessage.encode_length]
    omega
  | futuresQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesQuoteMessage.encode_length]
    omega
  | strategyQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyQuoteMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | futureOptionsMarketDepthMessage inner =>
    have bound_inner := FutureOptionsMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | futuresMarketDepthMessage inner =>
    have bound_inner := FuturesMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | strategyMarketDepthMessage inner =>
    have bound_inner := StrategyMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futureTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionInstrumentKeysMessage.encode_length]
    omega
  | futureOptionsInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsInstrumentKeysMessage.encode_length]
    omega
  | underlyingInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UnderlyingInstrumentKeysMessage.encode_length]
    omega
  | futuresInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesInstrumentKeysMessage.encode_length]
    omega
  | strategyInstrumentKeysMessage inner =>
    have bound_inner := StrategyInstrumentKeysMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionAuctionBeginningMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionAuctionBeginningMessage.encode_length]
    omega
  | strategyAuctionBeginningMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyAuctionBeginningMessage.encode_length]
    omega
  | optionSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionSummaryMessage.encode_length]
    omega
  | futureOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsSummaryMessage.encode_length]
    omega
  | futuresSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesSummaryMessage.encode_length]
    omega
  | strategySummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategySummaryMessage.encode_length]
    omega
  | optionInitialAndImprovementOrderMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionInitialAndImprovementOrderMessage.encode_length]
    omega
  | strategyInitialAndImprovementOrderMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyInitialAndImprovementOrderMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFutureOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfFutureOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFuturesSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfFuturesSummaryMessage.encode_length]
    omega
  | beginningOfStrategySummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfStrategySummaryMessage.encode_length]
    omega
  | optionAuctionEndingMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionAuctionEndingMessage.encode_length]
    omega
  | strategyAuctionEndingMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyAuctionEndingMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusStrategiesMessage.encode_length]
    omega
  | futureDeliverablesMessage inner =>
    have bound_inner := FutureDeliverablesMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | bulletinsMessage inner =>
    have bound_inner := BulletinsMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | endOfSalesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfSalesMessage.encode_length]
    omega
  | tickTableMessage inner =>
    have bound_inner := TickTableMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | endOfTransmissionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CircuitAssuranceMessage.encode_length]
    omega
  | startOfDayMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StartOfDayMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.TmxMxSolamulticastHsvfV114
