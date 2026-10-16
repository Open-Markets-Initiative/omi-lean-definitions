import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Orders v5.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesOrdersOuchV50Server

/-- Reject Reason Code: one byte code -/
def RejectReasonCode.codes : List UInt8 :=
  [0x41, 0x53]

inductive RejectReasonCode where
  | notAuthorized -- Not Authorized
  | sessionNotAvailable -- Session Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReasonCode

def toByte : RejectReasonCode → UInt8
  | .notAuthorized => 0x41
  | .sessionNotAvailable => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReasonCode :=
  if byte = 0x41 then .notAuthorized
  else .sessionNotAvailable

def ofByte (byte : UInt8) : RejectReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReasonCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | sessionNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReasonCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RejectReasonCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RejectReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReasonCode

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x53, 0x45]

inductive EventCode where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x53 then .startOfDay
  else .endOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EventCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .sellShort => 0x54
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x54 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | sellShort => decide
  | sellShortExempt => decide
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

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x30, 0x33, 0x35, 0x36, 0x45]

inductive TimeInForce where
  | day -- Day
  | ioc -- Ioc
  | gtxExtendedHours -- Gtx Extended Hours
  | gtt -- Gtt
  | afterHours -- After Hours
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .day => 0x30
  | .ioc => 0x33
  | .gtxExtendedHours => 0x35
  | .gtt => 0x36
  | .afterHours => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x30 then .day
  else if byte = 0x33 then .ioc
  else if byte = 0x35 then .gtxExtendedHours
  else if byte = 0x36 then .gtt
  else .afterHours

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | ioc => decide
  | gtxExtendedHours => decide
  | gtt => decide
  | afterHours => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TimeInForce) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x41, 0x59, 0x4E, 0x5A]

inductive Display where
  | attributable -- Attributable
  | visible -- Visible
  | hidden -- Hidden
  | conformant -- Conformant
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .attributable => 0x41
  | .visible => 0x59
  | .hidden => 0x4E
  | .conformant => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x41 then .attributable
  else if byte = 0x59 then .visible
  else if byte = 0x4E then .hidden
  else .conformant

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | attributable => decide
  | visible => decide
  | hidden => decide
  | conformant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Display) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x4F, 0x41, 0x50, 0x52]

inductive Capacity where
  | other -- Other
  | agency -- Agency
  | principal -- Principal
  | riskless -- Riskless
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .other => 0x4F
  | .agency => 0x41
  | .principal => 0x50
  | .riskless => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x4F then .other
  else if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .riskless

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | other => decide
  | agency => decide
  | principal => decide
  | riskless => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Capacity) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

/-- Inter Market Sweep Eligibility: one byte code -/
def InterMarketSweepEligibility.codes : List UInt8 :=
  [0x59, 0x4E]

inductive InterMarketSweepEligibility where
  | eligible -- Eligible
  | notEligible -- Not Eligible
  | unlisted (byte : { byte : UInt8 // byte ∉ InterMarketSweepEligibility.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InterMarketSweepEligibility

def toByte : InterMarketSweepEligibility → UInt8
  | .eligible => 0x59
  | .notEligible => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InterMarketSweepEligibility :=
  if byte = 0x59 then .eligible
  else .notEligible

def ofByte (byte : UInt8) : InterMarketSweepEligibility :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InterMarketSweepEligibility) : ofByte value.toByte = value := by
  cases value with
  | eligible => decide
  | notEligible => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InterMarketSweepEligibility) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InterMarketSweepEligibility × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InterMarketSweepEligibility) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InterMarketSweepEligibility) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InterMarketSweepEligibility) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InterMarketSweepEligibility

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4E, 0x4F, 0x43, 0x48, 0x53, 0x52, 0x45, 0x41]

inductive CrossType where
  | continuousMarket -- Continuous Market
  | openingCross -- Opening Cross
  | closingCross -- Closing Cross
  | haltIpo -- Halt Ipo
  | supplemental -- Supplemental
  | retail -- Retail
  | extendedLife -- Extended Life
  | afterHoursClose -- After Hours Close
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .continuousMarket => 0x4E
  | .openingCross => 0x4F
  | .closingCross => 0x43
  | .haltIpo => 0x48
  | .supplemental => 0x53
  | .retail => 0x52
  | .extendedLife => 0x45
  | .afterHoursClose => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4E then .continuousMarket
  else if byte = 0x4F then .openingCross
  else if byte = 0x43 then .closingCross
  else if byte = 0x48 then .haltIpo
  else if byte = 0x53 then .supplemental
  else if byte = 0x52 then .retail
  else if byte = 0x45 then .extendedLife
  else .afterHoursClose

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | continuousMarket => decide
  | openingCross => decide
  | closingCross => decide
  | haltIpo => decide
  | supplemental => decide
  | retail => decide
  | extendedLife => decide
  | afterHoursClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CrossType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Order State: one byte code -/
def OrderState.codes : List UInt8 :=
  [0x4C, 0x44]

inductive OrderState where
  | orderLive -- Order Live
  | orderDead -- Order Dead
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderState

def toByte : OrderState → UInt8
  | .orderLive => 0x4C
  | .orderDead => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderState :=
  if byte = 0x4C then .orderLive
  else .orderDead

def ofByte (byte : UInt8) : OrderState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderState) : ofByte value.toByte = value := by
  cases value with
  | orderLive => decide
  | orderDead => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderState

/-- Customer Type: one byte code -/
def CustomerType.codes : List UInt8 :=
  [0x52, 0x4E]

inductive CustomerType where
  | retailDesignatedOrder -- Retail Designated Order
  | notRetailDesignated -- Not Retail Designated
  | unlisted (byte : { byte : UInt8 // byte ∉ CustomerType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustomerType

def toByte : CustomerType → UInt8
  | .retailDesignatedOrder => 0x52
  | .notRetailDesignated => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustomerType :=
  if byte = 0x52 then .retailDesignatedOrder
  else .notRetailDesignated

def ofByte (byte : UInt8) : CustomerType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustomerType) : ofByte value.toByte = value := by
  cases value with
  | retailDesignatedOrder => decide
  | notRetailDesignated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustomerType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustomerType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustomerType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CustomerType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CustomerType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustomerType

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x4C, 0x50, 0x4D, 0x52, 0x51, 0x6D]

inductive PriceType where
  | limit -- Limit
  | marketPeg -- Market Peg
  | midpointPeg -- Midpoint Peg
  | primaryPeg -- Primary Peg
  | marketMakerPeg -- Market Maker Peg
  | midpoint -- Midpoint
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .limit => 0x4C
  | .marketPeg => 0x50
  | .midpointPeg => 0x4D
  | .primaryPeg => 0x52
  | .marketMakerPeg => 0x51
  | .midpoint => 0x6D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x4C then .limit
  else if byte = 0x50 then .marketPeg
  else if byte = 0x4D then .midpointPeg
  else if byte = 0x52 then .primaryPeg
  else if byte = 0x51 then .marketMakerPeg
  else .midpoint

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | limit => decide
  | marketPeg => decide
  | midpointPeg => decide
  | primaryPeg => decide
  | marketMakerPeg => decide
  | midpoint => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceType

/-- Discretion Price Type: one byte code -/
def DiscretionPriceType.codes : List UInt8 :=
  [0x4C, 0x50, 0x4D, 0x52]

inductive DiscretionPriceType where
  | limit -- Limit
  | marketPeg -- Market Peg
  | midpointPeg -- Midpoint Peg
  | primaryPeg -- Primary Peg
  | unlisted (byte : { byte : UInt8 // byte ∉ DiscretionPriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DiscretionPriceType

def toByte : DiscretionPriceType → UInt8
  | .limit => 0x4C
  | .marketPeg => 0x50
  | .midpointPeg => 0x4D
  | .primaryPeg => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DiscretionPriceType :=
  if byte = 0x4C then .limit
  else if byte = 0x50 then .marketPeg
  else if byte = 0x4D then .midpointPeg
  else .primaryPeg

def ofByte (byte : UInt8) : DiscretionPriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DiscretionPriceType) : ofByte value.toByte = value := by
  cases value with
  | limit => decide
  | marketPeg => decide
  | midpointPeg => decide
  | primaryPeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DiscretionPriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DiscretionPriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DiscretionPriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DiscretionPriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DiscretionPriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DiscretionPriceType

/-- Post Only: one byte code -/
def PostOnly.codes : List UInt8 :=
  [0x50, 0x4E]

inductive PostOnly where
  | postOnly -- Post Only
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ PostOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PostOnly

def toByte : PostOnly → UInt8
  | .postOnly => 0x50
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PostOnly :=
  if byte = 0x50 then .postOnly
  else .no

def ofByte (byte : UInt8) : PostOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PostOnly) : ofByte value.toByte = value := by
  cases value with
  | postOnly => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PostOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PostOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PostOnly) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PostOnly) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PostOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PostOnly

/-- Trade Now: one byte code -/
def TradeNow.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TradeNow where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeNow.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeNow

def toByte : TradeNow → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeNow :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : TradeNow :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeNow) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeNow) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeNow × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeNow) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeNow) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeNow) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeNow

/-- Handle Inst: one byte code -/
def HandleInst.codes : List UInt8 :=
  [0x49, 0x4F, 0x54, 0x51, 0x42, 0x44]

inductive HandleInst where
  | imbalanceOnly -- Imbalance Only
  | retailOrderType1 -- Retail Order Type 1
  | retailOrderType2 -- Retail Order Type 2
  | retailPriceImprovement -- Retail Price Improvement
  | extendedLifeContinuous -- Extended Life Continuous
  | directListingCapitalRaise -- Direct Listing Capital Raise
  | unlisted (byte : { byte : UInt8 // byte ∉ HandleInst.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HandleInst

def toByte : HandleInst → UInt8
  | .imbalanceOnly => 0x49
  | .retailOrderType1 => 0x4F
  | .retailOrderType2 => 0x54
  | .retailPriceImprovement => 0x51
  | .extendedLifeContinuous => 0x42
  | .directListingCapitalRaise => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HandleInst :=
  if byte = 0x49 then .imbalanceOnly
  else if byte = 0x4F then .retailOrderType1
  else if byte = 0x54 then .retailOrderType2
  else if byte = 0x51 then .retailPriceImprovement
  else if byte = 0x42 then .extendedLifeContinuous
  else .directListingCapitalRaise

def ofByte (byte : UInt8) : HandleInst :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HandleInst) : ofByte value.toByte = value := by
  cases value with
  | imbalanceOnly => decide
  | retailOrderType1 => decide
  | retailOrderType2 => decide
  | retailPriceImprovement => decide
  | extendedLifeContinuous => decide
  | directListingCapitalRaise => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HandleInst) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HandleInst × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HandleInst) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : HandleInst) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : HandleInst) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HandleInst

/-- Bbo Weight Indicator: one byte code -/
def BboWeightIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x20, 0x53, 0x4E]

inductive BboWeightIndicator where
  | weight0To02Percent -- Weight 0 To 0.2 Percent
  | weight02To1Percent -- Weight 0.2 To 1 Percent
  | weight1To2Percent -- Weight 1 To 2 Percent
  | greaterThan2 -- Greater Than 2%
  | unspecified -- Unspecified
  | setsTheQbboWhileJoiningTheNbbo -- Sets The Qbbo While Joining The Nbbo
  | improvesTheNbboUponEntry -- Improves The Nbbo Upon Entry
  | unlisted (byte : { byte : UInt8 // byte ∉ BboWeightIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BboWeightIndicator

def toByte : BboWeightIndicator → UInt8
  | .weight0To02Percent => 0x30
  | .weight02To1Percent => 0x31
  | .weight1To2Percent => 0x32
  | .greaterThan2 => 0x33
  | .unspecified => 0x20
  | .setsTheQbboWhileJoiningTheNbbo => 0x53
  | .improvesTheNbboUponEntry => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BboWeightIndicator :=
  if byte = 0x30 then .weight0To02Percent
  else if byte = 0x31 then .weight02To1Percent
  else if byte = 0x32 then .weight1To2Percent
  else if byte = 0x33 then .greaterThan2
  else if byte = 0x20 then .unspecified
  else if byte = 0x53 then .setsTheQbboWhileJoiningTheNbbo
  else .improvesTheNbboUponEntry

def ofByte (byte : UInt8) : BboWeightIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BboWeightIndicator) : ofByte value.toByte = value := by
  cases value with
  | weight0To02Percent => decide
  | weight02To1Percent => decide
  | weight1To2Percent => decide
  | greaterThan2 => decide
  | unspecified => decide
  | setsTheQbboWhileJoiningTheNbbo => decide
  | improvesTheNbboUponEntry => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BboWeightIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BboWeightIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BboWeightIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BboWeightIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BboWeightIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BboWeightIndicator

/-- Shares Located: one byte code -/
def SharesLocated.codes : List UInt8 :=
  [0x59, 0x4E]

inductive SharesLocated where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ SharesLocated.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SharesLocated

def toByte : SharesLocated → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SharesLocated :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : SharesLocated :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SharesLocated) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SharesLocated) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SharesLocated × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SharesLocated) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SharesLocated) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SharesLocated) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SharesLocated

/-- Aiq Strategy: one byte code -/
def AiqStrategy.codes : List UInt8 :=
  [0x2A, 0x4E, 0x59, 0x44, 0x4F, 0x57, 0x52, 0x79, 0x64, 0x6F, 0x77, 0x72, 0x5A, 0x45, 0x50, 0x58, 0x53, 0x30, 0x31, 0x32, 0x34, 0x35]

inductive AiqStrategy where
  | usePortDefault -- Use Port Default
  | disabled -- Disabled
  | firmLevelDecrementBothNoDetails -- Firm Level Decrement Both No Details
  | firmLevelDecrementBoth -- Firm Level Decrement Both
  | firmLevelCancelOldest -- Firm Level Cancel Oldest
  | firmLevelCancelNewest -- Firm Level Cancel Newest
  | firmLevelUseRemover -- Firm Level Use Remover
  | organizationLevelDecrementBothNoDetails -- Organization Level Decrement Both No Details
  | organizationLevelDecrementBoth -- Organization Level Decrement Both
  | organizationLevelCancelOldest -- Organization Level Cancel Oldest
  | organizationLevelCancelNewest -- Organization Level Cancel Newest
  | organizationLevelUseRemover -- Organization Level Use Remover
  | affiliateLevelDecrementBothNoDetails -- Affiliate Level Decrement Both No Details
  | affiliateLevelDecrementBoth -- Affiliate Level Decrement Both
  | affiliateLevelCancelOldest -- Affiliate Level Cancel Oldest
  | affiliateLevelCancelNewest -- Affiliate Level Cancel Newest
  | affiliateLevelUseRemover -- Affiliate Level Use Remover
  | matchAnyLevelDecrementBothNoDetails -- Match Any Level Decrement Both No Details
  | matchAnyLevelDecrementBoth -- Match Any Level Decrement Both
  | matchAnyLevelCancelOldest -- Match Any Level Cancel Oldest
  | matchAnyLevelCancelNewest -- Match Any Level Cancel Newest
  | matchAnyLevelUseRemover -- Match Any Level Use Remover
  | unlisted (byte : { byte : UInt8 // byte ∉ AiqStrategy.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AiqStrategy

def toByte : AiqStrategy → UInt8
  | .usePortDefault => 0x2A
  | .disabled => 0x4E
  | .firmLevelDecrementBothNoDetails => 0x59
  | .firmLevelDecrementBoth => 0x44
  | .firmLevelCancelOldest => 0x4F
  | .firmLevelCancelNewest => 0x57
  | .firmLevelUseRemover => 0x52
  | .organizationLevelDecrementBothNoDetails => 0x79
  | .organizationLevelDecrementBoth => 0x64
  | .organizationLevelCancelOldest => 0x6F
  | .organizationLevelCancelNewest => 0x77
  | .organizationLevelUseRemover => 0x72
  | .affiliateLevelDecrementBothNoDetails => 0x5A
  | .affiliateLevelDecrementBoth => 0x45
  | .affiliateLevelCancelOldest => 0x50
  | .affiliateLevelCancelNewest => 0x58
  | .affiliateLevelUseRemover => 0x53
  | .matchAnyLevelDecrementBothNoDetails => 0x30
  | .matchAnyLevelDecrementBoth => 0x31
  | .matchAnyLevelCancelOldest => 0x32
  | .matchAnyLevelCancelNewest => 0x34
  | .matchAnyLevelUseRemover => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AiqStrategy :=
  if byte = 0x2A then .usePortDefault
  else if byte = 0x4E then .disabled
  else if byte = 0x59 then .firmLevelDecrementBothNoDetails
  else if byte = 0x44 then .firmLevelDecrementBoth
  else if byte = 0x4F then .firmLevelCancelOldest
  else if byte = 0x57 then .firmLevelCancelNewest
  else if byte = 0x52 then .firmLevelUseRemover
  else if byte = 0x79 then .organizationLevelDecrementBothNoDetails
  else if byte = 0x64 then .organizationLevelDecrementBoth
  else if byte = 0x6F then .organizationLevelCancelOldest
  else if byte = 0x77 then .organizationLevelCancelNewest
  else if byte = 0x72 then .organizationLevelUseRemover
  else if byte = 0x5A then .affiliateLevelDecrementBothNoDetails
  else if byte = 0x45 then .affiliateLevelDecrementBoth
  else if byte = 0x50 then .affiliateLevelCancelOldest
  else if byte = 0x58 then .affiliateLevelCancelNewest
  else if byte = 0x53 then .affiliateLevelUseRemover
  else if byte = 0x30 then .matchAnyLevelDecrementBothNoDetails
  else if byte = 0x31 then .matchAnyLevelDecrementBoth
  else if byte = 0x32 then .matchAnyLevelCancelOldest
  else if byte = 0x34 then .matchAnyLevelCancelNewest
  else .matchAnyLevelUseRemover

def ofByte (byte : UInt8) : AiqStrategy :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AiqStrategy) : ofByte value.toByte = value := by
  cases value with
  | usePortDefault => decide
  | disabled => decide
  | firmLevelDecrementBothNoDetails => decide
  | firmLevelDecrementBoth => decide
  | firmLevelCancelOldest => decide
  | firmLevelCancelNewest => decide
  | firmLevelUseRemover => decide
  | organizationLevelDecrementBothNoDetails => decide
  | organizationLevelDecrementBoth => decide
  | organizationLevelCancelOldest => decide
  | organizationLevelCancelNewest => decide
  | organizationLevelUseRemover => decide
  | affiliateLevelDecrementBothNoDetails => decide
  | affiliateLevelDecrementBoth => decide
  | affiliateLevelCancelOldest => decide
  | affiliateLevelCancelNewest => decide
  | affiliateLevelUseRemover => decide
  | matchAnyLevelDecrementBothNoDetails => decide
  | matchAnyLevelDecrementBoth => decide
  | matchAnyLevelCancelOldest => decide
  | matchAnyLevelCancelNewest => decide
  | matchAnyLevelUseRemover => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AiqStrategy) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AiqStrategy × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AiqStrategy) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AiqStrategy) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AiqStrategy) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AiqStrategy

/-- Cancel Order Reason: one byte code -/
def CancelOrderReason.codes : List UInt8 :=
  [0x55, 0x49, 0x54, 0x53, 0x44, 0x51, 0x5A, 0x4B, 0x48, 0x58, 0x45, 0x46, 0x47, 0x65]

inductive CancelOrderReason where
  | userRequestedCancel -- User Requested Cancel
  | immediateOrCancelOrder -- Immediate Or Cancel Order
  | timeout -- Timeout
  | supervisory -- Supervisory
  | regulatoryRestriction -- Regulatory Restriction
  | selfMatchPrevention -- Self Match Prevention
  | systemCancel -- System Cancel
  | thisOrderCannotBeExecuted -- This Order Cannot Be Executed
  | halted -- Halted
  | openProtection -- Open Protection
  | closed -- Closed
  | postOnlyCancel -- Post Only Cancel
  | postOnlyCancelContraSideDisplayed -- Post Only Cancel Contra Side Displayed
  | companyDirectListingCapitalRaiseOrderExceedsAllowableSharesOffered -- Company Direct Listing Capital Raise Order Exceeds Allowable Shares Offered
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelOrderReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelOrderReason

def toByte : CancelOrderReason → UInt8
  | .userRequestedCancel => 0x55
  | .immediateOrCancelOrder => 0x49
  | .timeout => 0x54
  | .supervisory => 0x53
  | .regulatoryRestriction => 0x44
  | .selfMatchPrevention => 0x51
  | .systemCancel => 0x5A
  | .thisOrderCannotBeExecuted => 0x4B
  | .halted => 0x48
  | .openProtection => 0x58
  | .closed => 0x45
  | .postOnlyCancel => 0x46
  | .postOnlyCancelContraSideDisplayed => 0x47
  | .companyDirectListingCapitalRaiseOrderExceedsAllowableSharesOffered => 0x65
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelOrderReason :=
  if byte = 0x55 then .userRequestedCancel
  else if byte = 0x49 then .immediateOrCancelOrder
  else if byte = 0x54 then .timeout
  else if byte = 0x53 then .supervisory
  else if byte = 0x44 then .regulatoryRestriction
  else if byte = 0x51 then .selfMatchPrevention
  else if byte = 0x5A then .systemCancel
  else if byte = 0x4B then .thisOrderCannotBeExecuted
  else if byte = 0x48 then .halted
  else if byte = 0x58 then .openProtection
  else if byte = 0x45 then .closed
  else if byte = 0x46 then .postOnlyCancel
  else if byte = 0x47 then .postOnlyCancelContraSideDisplayed
  else .companyDirectListingCapitalRaiseOrderExceedsAllowableSharesOffered

def ofByte (byte : UInt8) : CancelOrderReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelOrderReason) : ofByte value.toByte = value := by
  cases value with
  | userRequestedCancel => decide
  | immediateOrCancelOrder => decide
  | timeout => decide
  | supervisory => decide
  | regulatoryRestriction => decide
  | selfMatchPrevention => decide
  | systemCancel => decide
  | thisOrderCannotBeExecuted => decide
  | halted => decide
  | openProtection => decide
  | closed => decide
  | postOnlyCancel => decide
  | postOnlyCancelContraSideDisplayed => decide
  | companyDirectListingCapitalRaiseOrderExceedsAllowableSharesOffered => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelOrderReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelOrderReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelOrderReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CancelOrderReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CancelOrderReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelOrderReason

/-- Liquidity Flag: one byte code -/
def LiquidityFlag.codes : List UInt8 :=
  [0x41, 0x43, 0x65, 0x48, 0x69, 0x4A, 0x6A, 0x6B, 0x4B, 0x4C, 0x4D, 0x6D, 0x4E, 0x6E, 0x4F, 0x70, 0x71, 0x52, 0x72, 0x74, 0x75, 0x30, 0x37, 0x38, 0x31, 0x32, 0x33, 0x35, 0x39]

inductive LiquidityFlag where
  | added -- Added
  | closing -- Closing
  | retailDesignated -- Retail Designated
  | haltIpo -- Halt Ipo
  | afterHoursClosing -- After Hours Closing
  | nondisplayedAddingLiquidity -- Nondisplayed Adding Liquidity
  | rpiOrderProvidesLiquidity -- Rpi Order Provides Liquidity
  | addedLiquidityViaAMidpointOrder -- Added Liquidity Via A Midpoint Order
  | haltCross -- Halt Cross
  | closingCross -- Closing Cross
  | openingCross -- Opening Cross
  | removedLiquidityAtAMidpoint -- Removed Liquidity At A Midpoint
  | passiveMidpointExecution -- Passive Midpoint Execution
  | midpointExtendedLifeOrderExecution -- Midpoint Extended Life Order Execution
  | opening -- Opening
  | removedPriceImprovingNondisplayedLiquidity -- Removed Price Improving Nondisplayed Liquidity
  | rmoRetailOrderRemovesNonRpiMidpointLiquidity -- Rmo Retail Order Removes Non Rpi Midpoint Liquidity
  | removed -- Removed
  | retailOrderRemovesRpiLiquidity -- Retail Order Removes Rpi Liquidity
  | retailOrderRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity -- Retail Order Removes Price Improving Nondisplayed Liquidity Other Than Rpi Liquidity
  | addedNondisplayedLiquidityViaAReserveOrder -- Added Nondisplayed Liquidity Via A Reserve Order
  | supplemental -- Supplemental
  | displayedLiquidityaddingOrderImprovesTheNbbo -- Displayed Liquidityadding Order Improves The Nbbo
  | displayedLiquidityaddingOrderSetsTheQbboWhileJoiningTheNbbo -- Displayed Liquidityadding Order Sets The Qbbo While Joining The Nbbo
  | rpiOrderProvidesLiquidityNoRpii -- Rpi Order Provides Liquidity No Rpii
  | addedInThePremarket -- Added In The Premarket
  | removedInThePremarket -- Removed In The Premarket
  | displayedLiquidityaddingOrderImprovesTheNbboInThePremarket -- Displayed Liquidityadding Order Improves The Nbbo In The Premarket
  | nondisplayedAddingLiquidityInThePremarket -- Nondisplayed Adding Liquidity In The Premarket
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityFlag

def toByte : LiquidityFlag → UInt8
  | .added => 0x41
  | .closing => 0x43
  | .retailDesignated => 0x65
  | .haltIpo => 0x48
  | .afterHoursClosing => 0x69
  | .nondisplayedAddingLiquidity => 0x4A
  | .rpiOrderProvidesLiquidity => 0x6A
  | .addedLiquidityViaAMidpointOrder => 0x6B
  | .haltCross => 0x4B
  | .closingCross => 0x4C
  | .openingCross => 0x4D
  | .removedLiquidityAtAMidpoint => 0x6D
  | .passiveMidpointExecution => 0x4E
  | .midpointExtendedLifeOrderExecution => 0x6E
  | .opening => 0x4F
  | .removedPriceImprovingNondisplayedLiquidity => 0x70
  | .rmoRetailOrderRemovesNonRpiMidpointLiquidity => 0x71
  | .removed => 0x52
  | .retailOrderRemovesRpiLiquidity => 0x72
  | .retailOrderRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity => 0x74
  | .addedNondisplayedLiquidityViaAReserveOrder => 0x75
  | .supplemental => 0x30
  | .displayedLiquidityaddingOrderImprovesTheNbbo => 0x37
  | .displayedLiquidityaddingOrderSetsTheQbboWhileJoiningTheNbbo => 0x38
  | .rpiOrderProvidesLiquidityNoRpii => 0x31
  | .addedInThePremarket => 0x32
  | .removedInThePremarket => 0x33
  | .displayedLiquidityaddingOrderImprovesTheNbboInThePremarket => 0x35
  | .nondisplayedAddingLiquidityInThePremarket => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityFlag :=
  if byte = 0x41 then .added
  else if byte = 0x43 then .closing
  else if byte = 0x65 then .retailDesignated
  else if byte = 0x48 then .haltIpo
  else if byte = 0x69 then .afterHoursClosing
  else if byte = 0x4A then .nondisplayedAddingLiquidity
  else if byte = 0x6A then .rpiOrderProvidesLiquidity
  else if byte = 0x6B then .addedLiquidityViaAMidpointOrder
  else if byte = 0x4B then .haltCross
  else if byte = 0x4C then .closingCross
  else if byte = 0x4D then .openingCross
  else if byte = 0x6D then .removedLiquidityAtAMidpoint
  else if byte = 0x4E then .passiveMidpointExecution
  else if byte = 0x6E then .midpointExtendedLifeOrderExecution
  else if byte = 0x4F then .opening
  else if byte = 0x70 then .removedPriceImprovingNondisplayedLiquidity
  else if byte = 0x71 then .rmoRetailOrderRemovesNonRpiMidpointLiquidity
  else if byte = 0x52 then .removed
  else if byte = 0x72 then .retailOrderRemovesRpiLiquidity
  else if byte = 0x74 then .retailOrderRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity
  else if byte = 0x75 then .addedNondisplayedLiquidityViaAReserveOrder
  else if byte = 0x30 then .supplemental
  else if byte = 0x37 then .displayedLiquidityaddingOrderImprovesTheNbbo
  else if byte = 0x38 then .displayedLiquidityaddingOrderSetsTheQbboWhileJoiningTheNbbo
  else if byte = 0x31 then .rpiOrderProvidesLiquidityNoRpii
  else if byte = 0x32 then .addedInThePremarket
  else if byte = 0x33 then .removedInThePremarket
  else if byte = 0x35 then .displayedLiquidityaddingOrderImprovesTheNbboInThePremarket
  else .nondisplayedAddingLiquidityInThePremarket

def ofByte (byte : UInt8) : LiquidityFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityFlag) : ofByte value.toByte = value := by
  cases value with
  | added => decide
  | closing => decide
  | retailDesignated => decide
  | haltIpo => decide
  | afterHoursClosing => decide
  | nondisplayedAddingLiquidity => decide
  | rpiOrderProvidesLiquidity => decide
  | addedLiquidityViaAMidpointOrder => decide
  | haltCross => decide
  | closingCross => decide
  | openingCross => decide
  | removedLiquidityAtAMidpoint => decide
  | passiveMidpointExecution => decide
  | midpointExtendedLifeOrderExecution => decide
  | opening => decide
  | removedPriceImprovingNondisplayedLiquidity => decide
  | rmoRetailOrderRemovesNonRpiMidpointLiquidity => decide
  | removed => decide
  | retailOrderRemovesRpiLiquidity => decide
  | retailOrderRemovesPriceImprovingNondisplayedLiquidityOtherThanRpiLiquidity => decide
  | addedNondisplayedLiquidityViaAReserveOrder => decide
  | supplemental => decide
  | displayedLiquidityaddingOrderImprovesTheNbbo => decide
  | displayedLiquidityaddingOrderSetsTheQbboWhileJoiningTheNbbo => decide
  | rpiOrderProvidesLiquidityNoRpii => decide
  | addedInThePremarket => decide
  | removedInThePremarket => decide
  | displayedLiquidityaddingOrderImprovesTheNbboInThePremarket => decide
  | nondisplayedAddingLiquidityInThePremarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LiquidityFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LiquidityFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityFlag

/-- Broken Trade Reason: one byte code -/
def BrokenTradeReason.codes : List UInt8 :=
  [0x45, 0x43, 0x53, 0x58]

inductive BrokenTradeReason where
  | erroneous -- Erroneous
  | consent -- Consent
  | supervisory -- Supervisory
  | external -- External
  | unlisted (byte : { byte : UInt8 // byte ∉ BrokenTradeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BrokenTradeReason

def toByte : BrokenTradeReason → UInt8
  | .erroneous => 0x45
  | .consent => 0x43
  | .supervisory => 0x53
  | .external => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BrokenTradeReason :=
  if byte = 0x45 then .erroneous
  else if byte = 0x43 then .consent
  else if byte = 0x53 then .supervisory
  else .external

def ofByte (byte : UInt8) : BrokenTradeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BrokenTradeReason) : ofByte value.toByte = value := by
  cases value with
  | erroneous => decide
  | consent => decide
  | supervisory => decide
  | external => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BrokenTradeReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BrokenTradeReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BrokenTradeReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BrokenTradeReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BrokenTradeReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BrokenTradeReason

/-- Order Restated Reason: one byte code -/
def OrderRestatedReason.codes : List UInt8 :=
  [0x52, 0x50]

inductive OrderRestatedReason where
  | refreshOfDisplay -- Refresh Of Display
  | updateOfDisplayedPrice -- Update Of Displayed Price
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderRestatedReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderRestatedReason

def toByte : OrderRestatedReason → UInt8
  | .refreshOfDisplay => 0x52
  | .updateOfDisplayedPrice => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderRestatedReason :=
  if byte = 0x52 then .refreshOfDisplay
  else .updateOfDisplayedPrice

def ofByte (byte : UInt8) : OrderRestatedReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderRestatedReason) : ofByte value.toByte = value := by
  cases value with
  | refreshOfDisplay => decide
  | updateOfDisplayedPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderRestatedReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderRestatedReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderRestatedReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderRestatedReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderRestatedReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderRestatedReason

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65535
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65535 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65535 := by
  have bound_debugText := message.debugText.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.debugText.length_le]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginAcceptedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : RejectReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  RejectReasonCode.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← RejectReasonCode.decode bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [RejectReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RejectReasonCode.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRejectedPacket

/-- System Event Message: 9 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SystemEventMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SystemEventMessage

/-- Firm: 4 bytes -/
structure FirmValue where
  firm : Alpha 4
  deriving DecidableEq, Repr

namespace FirmValue

def encode (message : FirmValue) : List UInt8 :=
  Alpha.encode message.firm

def decode (bytes : List UInt8) : Option (FirmValue × List UInt8) := do
  let (firm, bytes) ← Alpha.decode 4 bytes
  pure ({ firm }, bytes)

@[simp] theorem encode_length (message : FirmValue) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : FirmValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FirmValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end FirmValue

/-- Min Qty: 4 bytes -/
structure MinQtyValue where
  minQty : BitVec 32
  deriving DecidableEq, Repr

namespace MinQtyValue

def encode (message : MinQtyValue) : List UInt8 :=
  encodeUInt 4 message.minQty

def decode (bytes : List UInt8) : Option (MinQtyValue × List UInt8) := do
  let (minQty, bytes) ← decodeUInt 4 bytes
  pure ({ minQty }, bytes)

@[simp] theorem encode_length (message : MinQtyValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MinQtyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinQtyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinQtyValue

/-- Customer Type: 1 bytes -/
structure CustomerTypeValue where
  customerType : CustomerType
  deriving DecidableEq, Repr

namespace CustomerTypeValue

def encode (message : CustomerTypeValue) : List UInt8 :=
  CustomerType.encode message.customerType

def decode (bytes : List UInt8) : Option (CustomerTypeValue × List UInt8) := do
  let (customerType, bytes) ← CustomerType.decode bytes
  pure ({ customerType }, bytes)

@[simp] theorem encode_length (message : CustomerTypeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [CustomerType.encode_length]

theorem encode_length_pos (message : CustomerTypeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomerTypeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [CustomerType.decode_encode, some_bind]
  rfl

end CustomerTypeValue

/-- Max Floor: 4 bytes -/
structure MaxFloorValue where
  maxFloor : BitVec 32
  deriving DecidableEq, Repr

namespace MaxFloorValue

def encode (message : MaxFloorValue) : List UInt8 :=
  encodeUInt 4 message.maxFloor

def decode (bytes : List UInt8) : Option (MaxFloorValue × List UInt8) := do
  let (maxFloor, bytes) ← decodeUInt 4 bytes
  pure ({ maxFloor }, bytes)

@[simp] theorem encode_length (message : MaxFloorValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MaxFloorValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaxFloorValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaxFloorValue

/-- Price Type: 1 bytes -/
structure PriceTypeValue where
  priceType : PriceType
  deriving DecidableEq, Repr

namespace PriceTypeValue

def encode (message : PriceTypeValue) : List UInt8 :=
  PriceType.encode message.priceType

def decode (bytes : List UInt8) : Option (PriceTypeValue × List UInt8) := do
  let (priceType, bytes) ← PriceType.decode bytes
  pure ({ priceType }, bytes)

@[simp] theorem encode_length (message : PriceTypeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [PriceType.encode_length]

theorem encode_length_pos (message : PriceTypeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceTypeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PriceType.decode_encode, some_bind]
  rfl

end PriceTypeValue

/-- Peg Offset: 4 bytes -/
structure PegOffsetValue where
  pegOffset : BitVec 32
  deriving DecidableEq, Repr

namespace PegOffsetValue

def encode (message : PegOffsetValue) : List UInt8 :=
  encodeUInt 4 message.pegOffset

def decode (bytes : List UInt8) : Option (PegOffsetValue × List UInt8) := do
  let (pegOffset, bytes) ← decodeUInt 4 bytes
  pure ({ pegOffset }, bytes)

@[simp] theorem encode_length (message : PegOffsetValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : PegOffsetValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PegOffsetValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PegOffsetValue

/-- Discretion Price: 8 bytes -/
structure DiscretionPriceValue where
  discretionPrice : BitVec 64
  deriving DecidableEq, Repr

namespace DiscretionPriceValue

def encode (message : DiscretionPriceValue) : List UInt8 :=
  encodeUInt 8 message.discretionPrice

def decode (bytes : List UInt8) : Option (DiscretionPriceValue × List UInt8) := do
  let (discretionPrice, bytes) ← decodeUInt 8 bytes
  pure ({ discretionPrice }, bytes)

@[simp] theorem encode_length (message : DiscretionPriceValue) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DiscretionPriceValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DiscretionPriceValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DiscretionPriceValue

/-- Discretion Price Type: 1 bytes -/
structure DiscretionPriceTypeValue where
  discretionPriceType : DiscretionPriceType
  deriving DecidableEq, Repr

namespace DiscretionPriceTypeValue

def encode (message : DiscretionPriceTypeValue) : List UInt8 :=
  DiscretionPriceType.encode message.discretionPriceType

def decode (bytes : List UInt8) : Option (DiscretionPriceTypeValue × List UInt8) := do
  let (discretionPriceType, bytes) ← DiscretionPriceType.decode bytes
  pure ({ discretionPriceType }, bytes)

@[simp] theorem encode_length (message : DiscretionPriceTypeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [DiscretionPriceType.encode_length]

theorem encode_length_pos (message : DiscretionPriceTypeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DiscretionPriceTypeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [DiscretionPriceType.decode_encode, some_bind]
  rfl

end DiscretionPriceTypeValue

/-- Discretion Peg Offset: 4 bytes -/
structure DiscretionPegOffsetValue where
  discretionPegOffset : BitVec 32
  deriving DecidableEq, Repr

namespace DiscretionPegOffsetValue

def encode (message : DiscretionPegOffsetValue) : List UInt8 :=
  encodeUInt 4 message.discretionPegOffset

def decode (bytes : List UInt8) : Option (DiscretionPegOffsetValue × List UInt8) := do
  let (discretionPegOffset, bytes) ← decodeUInt 4 bytes
  pure ({ discretionPegOffset }, bytes)

@[simp] theorem encode_length (message : DiscretionPegOffsetValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DiscretionPegOffsetValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DiscretionPegOffsetValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DiscretionPegOffsetValue

/-- Post Only: 1 bytes -/
structure PostOnlyValue where
  postOnly : PostOnly
  deriving DecidableEq, Repr

namespace PostOnlyValue

def encode (message : PostOnlyValue) : List UInt8 :=
  PostOnly.encode message.postOnly

def decode (bytes : List UInt8) : Option (PostOnlyValue × List UInt8) := do
  let (postOnly_, bytes) ← PostOnly.decode bytes
  pure ({ postOnly := postOnly_ }, bytes)

@[simp] theorem encode_length (message : PostOnlyValue) : (encode message).length = 1 := by
  unfold encode
  simp only [PostOnly.encode_length]

theorem encode_length_pos (message : PostOnlyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PostOnlyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PostOnly.decode_encode, some_bind]
  rfl

end PostOnlyValue

/-- Random Reserves: 4 bytes -/
structure RandomReservesValue where
  randomReserves : BitVec 32
  deriving DecidableEq, Repr

namespace RandomReservesValue

def encode (message : RandomReservesValue) : List UInt8 :=
  encodeUInt 4 message.randomReserves

def decode (bytes : List UInt8) : Option (RandomReservesValue × List UInt8) := do
  let (randomReserves, bytes) ← decodeUInt 4 bytes
  pure ({ randomReserves }, bytes)

@[simp] theorem encode_length (message : RandomReservesValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : RandomReservesValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RandomReservesValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RandomReservesValue

/-- Route: 4 bytes -/
structure RouteValue where
  route : Alpha 4
  deriving DecidableEq, Repr

namespace RouteValue

def encode (message : RouteValue) : List UInt8 :=
  Alpha.encode message.route

def decode (bytes : List UInt8) : Option (RouteValue × List UInt8) := do
  let (route, bytes) ← Alpha.decode 4 bytes
  pure ({ route }, bytes)

@[simp] theorem encode_length (message : RouteValue) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : RouteValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RouteValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end RouteValue

/-- Expire Time: 4 bytes -/
structure ExpireTimeValue where
  expireTime : BitVec 32
  deriving DecidableEq, Repr

namespace ExpireTimeValue

def encode (message : ExpireTimeValue) : List UInt8 :=
  encodeUInt 4 message.expireTime

def decode (bytes : List UInt8) : Option (ExpireTimeValue × List UInt8) := do
  let (expireTime, bytes) ← decodeUInt 4 bytes
  pure ({ expireTime }, bytes)

@[simp] theorem encode_length (message : ExpireTimeValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ExpireTimeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExpireTimeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExpireTimeValue

/-- Trade Now: 1 bytes -/
structure TradeNowValue where
  tradeNow : TradeNow
  deriving DecidableEq, Repr

namespace TradeNowValue

def encode (message : TradeNowValue) : List UInt8 :=
  TradeNow.encode message.tradeNow

def decode (bytes : List UInt8) : Option (TradeNowValue × List UInt8) := do
  let (tradeNow, bytes) ← TradeNow.decode bytes
  pure ({ tradeNow }, bytes)

@[simp] theorem encode_length (message : TradeNowValue) : (encode message).length = 1 := by
  unfold encode
  simp only [TradeNow.encode_length]

theorem encode_length_pos (message : TradeNowValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeNowValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [TradeNow.decode_encode, some_bind]
  rfl

end TradeNowValue

/-- Handle Inst: 1 bytes -/
structure HandleInstValue where
  handleInst : HandleInst
  deriving DecidableEq, Repr

namespace HandleInstValue

def encode (message : HandleInstValue) : List UInt8 :=
  HandleInst.encode message.handleInst

def decode (bytes : List UInt8) : Option (HandleInstValue × List UInt8) := do
  let (handleInst, bytes) ← HandleInst.decode bytes
  pure ({ handleInst }, bytes)

@[simp] theorem encode_length (message : HandleInstValue) : (encode message).length = 1 := by
  unfold encode
  simp only [HandleInst.encode_length]

theorem encode_length_pos (message : HandleInstValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HandleInstValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [HandleInst.decode_encode, some_bind]
  rfl

end HandleInstValue

/-- Bbo Weight Indicator: 1 bytes -/
structure BboWeightIndicatorValue where
  bboWeightIndicator : BboWeightIndicator
  deriving DecidableEq, Repr

namespace BboWeightIndicatorValue

def encode (message : BboWeightIndicatorValue) : List UInt8 :=
  BboWeightIndicator.encode message.bboWeightIndicator

def decode (bytes : List UInt8) : Option (BboWeightIndicatorValue × List UInt8) := do
  let (bboWeightIndicator, bytes) ← BboWeightIndicator.decode bytes
  pure ({ bboWeightIndicator }, bytes)

@[simp] theorem encode_length (message : BboWeightIndicatorValue) : (encode message).length = 1 := by
  unfold encode
  simp only [BboWeightIndicator.encode_length]

theorem encode_length_pos (message : BboWeightIndicatorValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BboWeightIndicatorValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [BboWeightIndicator.decode_encode, some_bind]
  rfl

end BboWeightIndicatorValue

/-- Group Id: 2 bytes -/
structure GroupIdValue where
  groupId : BitVec 16
  deriving DecidableEq, Repr

namespace GroupIdValue

def encode (message : GroupIdValue) : List UInt8 :=
  encodeUInt 2 message.groupId

def decode (bytes : List UInt8) : Option (GroupIdValue × List UInt8) := do
  let (groupId, bytes) ← decodeUInt 2 bytes
  pure ({ groupId }, bytes)

@[simp] theorem encode_length (message : GroupIdValue) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : GroupIdValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupIdValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end GroupIdValue

/-- Shares Located: 1 bytes -/
structure SharesLocatedValue where
  sharesLocated : SharesLocated
  deriving DecidableEq, Repr

namespace SharesLocatedValue

def encode (message : SharesLocatedValue) : List UInt8 :=
  SharesLocated.encode message.sharesLocated

def decode (bytes : List UInt8) : Option (SharesLocatedValue × List UInt8) := do
  let (sharesLocated, bytes) ← SharesLocated.decode bytes
  pure ({ sharesLocated }, bytes)

@[simp] theorem encode_length (message : SharesLocatedValue) : (encode message).length = 1 := by
  unfold encode
  simp only [SharesLocated.encode_length]

theorem encode_length_pos (message : SharesLocatedValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SharesLocatedValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SharesLocated.decode_encode, some_bind]
  rfl

end SharesLocatedValue

/-- User Ref Idx: 1 bytes -/
structure UserRefIdxValue where
  userRefIdx : BitVec 8
  deriving DecidableEq, Repr

namespace UserRefIdxValue

def encode (message : UserRefIdxValue) : List UInt8 :=
  encodeUInt 1 message.userRefIdx

def decode (bytes : List UInt8) : Option (UserRefIdxValue × List UInt8) := do
  let (userRefIdx, bytes) ← decodeUInt 1 bytes
  pure ({ userRefIdx }, bytes)

@[simp] theorem encode_length (message : UserRefIdxValue) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : UserRefIdxValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserRefIdxValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UserRefIdxValue

/-- Aiq Strategy: 1 bytes -/
structure AiqStrategyValue where
  aiqStrategy : AiqStrategy
  deriving DecidableEq, Repr

namespace AiqStrategyValue

def encode (message : AiqStrategyValue) : List UInt8 :=
  AiqStrategy.encode message.aiqStrategy

def decode (bytes : List UInt8) : Option (AiqStrategyValue × List UInt8) := do
  let (aiqStrategy, bytes) ← AiqStrategy.decode bytes
  pure ({ aiqStrategy }, bytes)

@[simp] theorem encode_length (message : AiqStrategyValue) : (encode message).length = 1 := by
  unfold encode
  simp only [AiqStrategy.encode_length]

theorem encode_length_pos (message : AiqStrategyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AiqStrategyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [AiqStrategy.decode_encode, some_bind]
  rfl

end AiqStrategyValue

/-- Aiq Group Id: 2 bytes -/
structure AiqGroupIdValue where
  aiqGroupId : Alpha 2
  deriving DecidableEq, Repr

namespace AiqGroupIdValue

def encode (message : AiqGroupIdValue) : List UInt8 :=
  Alpha.encode message.aiqGroupId

def decode (bytes : List UInt8) : Option (AiqGroupIdValue × List UInt8) := do
  let (aiqGroupId, bytes) ← Alpha.decode 2 bytes
  pure ({ aiqGroupId }, bytes)

@[simp] theorem encode_length (message : AiqGroupIdValue) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : AiqGroupIdValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AiqGroupIdValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end AiqGroupIdValue

/-- Any Order Accepted Optional Value, selected by Order Accepted Optional Field -/
inductive OrderAcceptedOptionalValue where
  | firm (message : FirmValue) -- 2
  | minQty (message : MinQtyValue) -- 3
  | customerType (message : CustomerTypeValue) -- 4
  | maxFloor (message : MaxFloorValue) -- 5
  | priceType (message : PriceTypeValue) -- 6
  | pegOffset (message : PegOffsetValue) -- 7
  | discretionPrice (message : DiscretionPriceValue) -- 9
  | discretionPriceType (message : DiscretionPriceTypeValue) -- 10
  | discretionPegOffset (message : DiscretionPegOffsetValue) -- 11
  | postOnly (message : PostOnlyValue) -- 12
  | randomReserves (message : RandomReservesValue) -- 13
  | route (message : RouteValue) -- 14
  | expireTime (message : ExpireTimeValue) -- 15
  | tradeNow (message : TradeNowValue) -- 16
  | handleInst (message : HandleInstValue) -- 17
  | bboWeightIndicator (message : BboWeightIndicatorValue) -- 18
  | groupId (message : GroupIdValue) -- 24
  | sharesLocated (message : SharesLocatedValue) -- 25
  | userRefIdx (message : UserRefIdxValue) -- 28
  | aiqStrategy (message : AiqStrategyValue) -- 29
  | aiqGroupId (message : AiqGroupIdValue) -- 30
  deriving DecidableEq, Repr

namespace OrderAcceptedOptionalValue

/-- The Order Accepted Optional Field each message is sent under -/
def tag : OrderAcceptedOptionalValue → BitVec 8
  | .firm _ => 2
  | .minQty _ => 3
  | .customerType _ => 4
  | .maxFloor _ => 5
  | .priceType _ => 6
  | .pegOffset _ => 7
  | .discretionPrice _ => 9
  | .discretionPriceType _ => 10
  | .discretionPegOffset _ => 11
  | .postOnly _ => 12
  | .randomReserves _ => 13
  | .route _ => 14
  | .expireTime _ => 15
  | .tradeNow _ => 16
  | .handleInst _ => 17
  | .bboWeightIndicator _ => 18
  | .groupId _ => 24
  | .sharesLocated _ => 25
  | .userRefIdx _ => 28
  | .aiqStrategy _ => 29
  | .aiqGroupId _ => 30

def encode : OrderAcceptedOptionalValue → List UInt8
  | .firm message => FirmValue.encode message
  | .minQty message => MinQtyValue.encode message
  | .customerType message => CustomerTypeValue.encode message
  | .maxFloor message => MaxFloorValue.encode message
  | .priceType message => PriceTypeValue.encode message
  | .pegOffset message => PegOffsetValue.encode message
  | .discretionPrice message => DiscretionPriceValue.encode message
  | .discretionPriceType message => DiscretionPriceTypeValue.encode message
  | .discretionPegOffset message => DiscretionPegOffsetValue.encode message
  | .postOnly message => PostOnlyValue.encode message
  | .randomReserves message => RandomReservesValue.encode message
  | .route message => RouteValue.encode message
  | .expireTime message => ExpireTimeValue.encode message
  | .tradeNow message => TradeNowValue.encode message
  | .handleInst message => HandleInstValue.encode message
  | .bboWeightIndicator message => BboWeightIndicatorValue.encode message
  | .groupId message => GroupIdValue.encode message
  | .sharesLocated message => SharesLocatedValue.encode message
  | .userRefIdx message => UserRefIdxValue.encode message
  | .aiqStrategy message => AiqStrategyValue.encode message
  | .aiqGroupId message => AiqGroupIdValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderAcceptedOptionalValue) : (encode message).length ≤ 8 := by
  cases message with
  | firm inner =>
    simp only [encode, FirmValue.encode_length]
    omega
  | minQty inner =>
    simp only [encode, MinQtyValue.encode_length]
    omega
  | customerType inner =>
    simp only [encode, CustomerTypeValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [encode, MaxFloorValue.encode_length]
    omega
  | priceType inner =>
    simp only [encode, PriceTypeValue.encode_length]
    omega
  | pegOffset inner =>
    simp only [encode, PegOffsetValue.encode_length]
    omega
  | discretionPrice inner =>
    simp only [encode, DiscretionPriceValue.encode_length]
    omega
  | discretionPriceType inner =>
    simp only [encode, DiscretionPriceTypeValue.encode_length]
    omega
  | discretionPegOffset inner =>
    simp only [encode, DiscretionPegOffsetValue.encode_length]
    omega
  | postOnly inner =>
    simp only [encode, PostOnlyValue.encode_length]
    omega
  | randomReserves inner =>
    simp only [encode, RandomReservesValue.encode_length]
    omega
  | route inner =>
    simp only [encode, RouteValue.encode_length]
    omega
  | expireTime inner =>
    simp only [encode, ExpireTimeValue.encode_length]
    omega
  | tradeNow inner =>
    simp only [encode, TradeNowValue.encode_length]
    omega
  | handleInst inner =>
    simp only [encode, HandleInstValue.encode_length]
    omega
  | bboWeightIndicator inner =>
    simp only [encode, BboWeightIndicatorValue.encode_length]
    omega
  | groupId inner =>
    simp only [encode, GroupIdValue.encode_length]
    omega
  | sharesLocated inner =>
    simp only [encode, SharesLocatedValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega
  | aiqStrategy inner =>
    simp only [encode, AiqStrategyValue.encode_length]
    omega
  | aiqGroupId inner =>
    simp only [encode, AiqGroupIdValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderAcceptedOptionalValue × List UInt8) :=
  if tag = 2 then (FirmValue.decode bytes).map fun (message, rest) => (.firm message, rest)
  else if tag = 3 then (MinQtyValue.decode bytes).map fun (message, rest) => (.minQty message, rest)
  else if tag = 4 then (CustomerTypeValue.decode bytes).map fun (message, rest) => (.customerType message, rest)
  else if tag = 5 then (MaxFloorValue.decode bytes).map fun (message, rest) => (.maxFloor message, rest)
  else if tag = 6 then (PriceTypeValue.decode bytes).map fun (message, rest) => (.priceType message, rest)
  else if tag = 7 then (PegOffsetValue.decode bytes).map fun (message, rest) => (.pegOffset message, rest)
  else if tag = 9 then (DiscretionPriceValue.decode bytes).map fun (message, rest) => (.discretionPrice message, rest)
  else if tag = 10 then (DiscretionPriceTypeValue.decode bytes).map fun (message, rest) => (.discretionPriceType message, rest)
  else if tag = 11 then (DiscretionPegOffsetValue.decode bytes).map fun (message, rest) => (.discretionPegOffset message, rest)
  else if tag = 12 then (PostOnlyValue.decode bytes).map fun (message, rest) => (.postOnly message, rest)
  else if tag = 13 then (RandomReservesValue.decode bytes).map fun (message, rest) => (.randomReserves message, rest)
  else if tag = 14 then (RouteValue.decode bytes).map fun (message, rest) => (.route message, rest)
  else if tag = 15 then (ExpireTimeValue.decode bytes).map fun (message, rest) => (.expireTime message, rest)
  else if tag = 16 then (TradeNowValue.decode bytes).map fun (message, rest) => (.tradeNow message, rest)
  else if tag = 17 then (HandleInstValue.decode bytes).map fun (message, rest) => (.handleInst message, rest)
  else if tag = 18 then (BboWeightIndicatorValue.decode bytes).map fun (message, rest) => (.bboWeightIndicator message, rest)
  else if tag = 24 then (GroupIdValue.decode bytes).map fun (message, rest) => (.groupId message, rest)
  else if tag = 25 then (SharesLocatedValue.decode bytes).map fun (message, rest) => (.sharesLocated message, rest)
  else if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else if tag = 29 then (AiqStrategyValue.decode bytes).map fun (message, rest) => (.aiqStrategy message, rest)
  else if tag = 30 then (AiqGroupIdValue.decode bytes).map fun (message, rest) => (.aiqGroupId message, rest)
  else none

@[simp] theorem decode_encode (message : OrderAcceptedOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end OrderAcceptedOptionalValue

/-- Order Accepted Appendage -/
structure OrderAcceptedAppendage where
  orderAcceptedOptionalValue : OrderAcceptedOptionalValue
  deriving DecidableEq, Repr

namespace OrderAcceptedAppendage

def encodeBody (message : OrderAcceptedAppendage) : List UInt8 :=
  encodeUInt 1 (OrderAcceptedOptionalValue.tag message.orderAcceptedOptionalValue)
    ++ (OrderAcceptedOptionalValue.encode message.orderAcceptedOptionalValue)

def decodeBody (bytes : List UInt8) : Option (OrderAcceptedAppendage × List UInt8) := do
  let (orderAcceptedOptionalField, bytes) ← decodeUInt 1 bytes
  let (orderAcceptedOptionalValue, bytes) ← OrderAcceptedOptionalValue.decode orderAcceptedOptionalField bytes
  pure ({ orderAcceptedOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : OrderAcceptedAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderAcceptedOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OrderAcceptedAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.orderAcceptedOptionalValue with
  | firm inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, FirmValue.encode_length]
    omega
  | minQty inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyValue.encode_length]
    omega
  | customerType inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, CustomerTypeValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, MaxFloorValue.encode_length]
    omega
  | priceType inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, PriceTypeValue.encode_length]
    omega
  | pegOffset inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, PegOffsetValue.encode_length]
    omega
  | discretionPrice inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, DiscretionPriceValue.encode_length]
    omega
  | discretionPriceType inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, DiscretionPriceTypeValue.encode_length]
    omega
  | discretionPegOffset inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, DiscretionPegOffsetValue.encode_length]
    omega
  | postOnly inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, PostOnlyValue.encode_length]
    omega
  | randomReserves inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, RandomReservesValue.encode_length]
    omega
  | route inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, RouteValue.encode_length]
    omega
  | expireTime inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, ExpireTimeValue.encode_length]
    omega
  | tradeNow inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, TradeNowValue.encode_length]
    omega
  | handleInst inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, HandleInstValue.encode_length]
    omega
  | bboWeightIndicator inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, BboWeightIndicatorValue.encode_length]
    omega
  | groupId inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, GroupIdValue.encode_length]
    omega
  | sharesLocated inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, SharesLocatedValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega
  | aiqStrategy inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, AiqStrategyValue.encode_length]
    omega
  | aiqGroupId inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, AiqGroupIdValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : OrderAcceptedAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (OrderAcceptedAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : OrderAcceptedAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OrderAcceptedAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end OrderAcceptedAppendage

/-- Order Accepted Message -/
structure OrderAcceptedMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  side : Side
  quantity : BitVec 32
  symbol : Alpha 8
  price : BitVec 64
  timeInForce : TimeInForce
  display : Display
  orderReferenceNumber : BitVec 64
  capacity : Capacity
  interMarketSweepEligibility : InterMarketSweepEligibility
  crossType : CrossType
  orderState : OrderState
  clordid : Alpha 14
  orderAcceptedAppendage : Sized 2 OrderAcceptedAppendage.encode
  deriving DecidableEq, Repr

namespace OrderAcceptedMessage

def encode (message : OrderAcceptedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.price
    ++ (TimeInForce.encode message.timeInForce
    ++ (Display.encode message.display
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Capacity.encode message.capacity
    ++ (InterMarketSweepEligibility.encode message.interMarketSweepEligibility
    ++ (CrossType.encode message.crossType
    ++ (OrderState.encode message.orderState
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderAcceptedAppendage.encode message.orderAcceptedAppendage.val).length)
    ++ (encodeMany OrderAcceptedAppendage.encode message.orderAcceptedAppendage.val)))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcceptedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (display, bytes) ← Display.decode bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (interMarketSweepEligibility, bytes) ← InterMarketSweepEligibility.decode bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (clordid, bytes) ← Alpha.decode 14 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (orderAcceptedAppendage_, bytes) ← decodeSized OrderAcceptedAppendage.decode appendageLength.toNat bytes
  if fits_orderAcceptedAppendage : (encodeMany OrderAcceptedAppendage.encode orderAcceptedAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, side, quantity, symbol, price, timeInForce, display, orderReferenceNumber, capacity, interMarketSweepEligibility, crossType, orderState, clordid, orderAcceptedAppendage := ⟨orderAcceptedAppendage_, fits_orderAcceptedAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderAcceptedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderAcceptedMessage) : (encode message).length ≤ 65598 := by
  have bound_orderAcceptedAppendage := message.orderAcceptedAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Side.encode_length, Alpha.encode_length, TimeInForce.encode_length, Display.encode_length, Capacity.encode_length, InterMarketSweepEligibility.encode_length, CrossType.encode_length, OrderState.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InterMarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 OrderAcceptedAppendage.encode OrderAcceptedAppendage.decode OrderAcceptedAppendage.decode_encode OrderAcceptedAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.orderAcceptedAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderAcceptedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderAcceptedMessage

/-- Any Replaced Message Optional Value, selected by Replaced Message Optional Field -/
inductive ReplacedMessageOptionalValue where
  | firm (message : FirmValue) -- 2
  | minQty (message : MinQtyValue) -- 3
  | maxFloor (message : MaxFloorValue) -- 5
  | priceType (message : PriceTypeValue) -- 6
  | postOnly (message : PostOnlyValue) -- 12
  | expireTime (message : ExpireTimeValue) -- 15
  | tradeNow (message : TradeNowValue) -- 16
  | handleInst (message : HandleInstValue) -- 17
  | bboWeightIndicator (message : BboWeightIndicatorValue) -- 18
  | userRefIdx (message : UserRefIdxValue) -- 28
  | aiqStrategy (message : AiqStrategyValue) -- 29
  | aiqGroupId (message : AiqGroupIdValue) -- 30
  deriving DecidableEq, Repr

namespace ReplacedMessageOptionalValue

/-- The Replaced Message Optional Field each message is sent under -/
def tag : ReplacedMessageOptionalValue → BitVec 8
  | .firm _ => 2
  | .minQty _ => 3
  | .maxFloor _ => 5
  | .priceType _ => 6
  | .postOnly _ => 12
  | .expireTime _ => 15
  | .tradeNow _ => 16
  | .handleInst _ => 17
  | .bboWeightIndicator _ => 18
  | .userRefIdx _ => 28
  | .aiqStrategy _ => 29
  | .aiqGroupId _ => 30

def encode : ReplacedMessageOptionalValue → List UInt8
  | .firm message => FirmValue.encode message
  | .minQty message => MinQtyValue.encode message
  | .maxFloor message => MaxFloorValue.encode message
  | .priceType message => PriceTypeValue.encode message
  | .postOnly message => PostOnlyValue.encode message
  | .expireTime message => ExpireTimeValue.encode message
  | .tradeNow message => TradeNowValue.encode message
  | .handleInst message => HandleInstValue.encode message
  | .bboWeightIndicator message => BboWeightIndicatorValue.encode message
  | .userRefIdx message => UserRefIdxValue.encode message
  | .aiqStrategy message => AiqStrategyValue.encode message
  | .aiqGroupId message => AiqGroupIdValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ReplacedMessageOptionalValue) : (encode message).length ≤ 4 := by
  cases message with
  | firm inner =>
    simp only [encode, FirmValue.encode_length]
    omega
  | minQty inner =>
    simp only [encode, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [encode, MaxFloorValue.encode_length]
    omega
  | priceType inner =>
    simp only [encode, PriceTypeValue.encode_length]
    omega
  | postOnly inner =>
    simp only [encode, PostOnlyValue.encode_length]
    omega
  | expireTime inner =>
    simp only [encode, ExpireTimeValue.encode_length]
    omega
  | tradeNow inner =>
    simp only [encode, TradeNowValue.encode_length]
    omega
  | handleInst inner =>
    simp only [encode, HandleInstValue.encode_length]
    omega
  | bboWeightIndicator inner =>
    simp only [encode, BboWeightIndicatorValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega
  | aiqStrategy inner =>
    simp only [encode, AiqStrategyValue.encode_length]
    omega
  | aiqGroupId inner =>
    simp only [encode, AiqGroupIdValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ReplacedMessageOptionalValue × List UInt8) :=
  if tag = 2 then (FirmValue.decode bytes).map fun (message, rest) => (.firm message, rest)
  else if tag = 3 then (MinQtyValue.decode bytes).map fun (message, rest) => (.minQty message, rest)
  else if tag = 5 then (MaxFloorValue.decode bytes).map fun (message, rest) => (.maxFloor message, rest)
  else if tag = 6 then (PriceTypeValue.decode bytes).map fun (message, rest) => (.priceType message, rest)
  else if tag = 12 then (PostOnlyValue.decode bytes).map fun (message, rest) => (.postOnly message, rest)
  else if tag = 15 then (ExpireTimeValue.decode bytes).map fun (message, rest) => (.expireTime message, rest)
  else if tag = 16 then (TradeNowValue.decode bytes).map fun (message, rest) => (.tradeNow message, rest)
  else if tag = 17 then (HandleInstValue.decode bytes).map fun (message, rest) => (.handleInst message, rest)
  else if tag = 18 then (BboWeightIndicatorValue.decode bytes).map fun (message, rest) => (.bboWeightIndicator message, rest)
  else if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else if tag = 29 then (AiqStrategyValue.decode bytes).map fun (message, rest) => (.aiqStrategy message, rest)
  else if tag = 30 then (AiqGroupIdValue.decode bytes).map fun (message, rest) => (.aiqGroupId message, rest)
  else none

@[simp] theorem decode_encode (message : ReplacedMessageOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ReplacedMessageOptionalValue

/-- Replaced Message Appendage -/
structure ReplacedMessageAppendage where
  replacedMessageOptionalValue : ReplacedMessageOptionalValue
  deriving DecidableEq, Repr

namespace ReplacedMessageAppendage

def encodeBody (message : ReplacedMessageAppendage) : List UInt8 :=
  encodeUInt 1 (ReplacedMessageOptionalValue.tag message.replacedMessageOptionalValue)
    ++ (ReplacedMessageOptionalValue.encode message.replacedMessageOptionalValue)

def decodeBody (bytes : List UInt8) : Option (ReplacedMessageAppendage × List UInt8) := do
  let (replacedMessageOptionalField, bytes) ← decodeUInt 1 bytes
  let (replacedMessageOptionalValue, bytes) ← ReplacedMessageOptionalValue.decode replacedMessageOptionalField bytes
  pure ({ replacedMessageOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : ReplacedMessageAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReplacedMessageOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ReplacedMessageAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.replacedMessageOptionalValue with
  | firm inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, FirmValue.encode_length]
    omega
  | minQty inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, MaxFloorValue.encode_length]
    omega
  | priceType inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, PriceTypeValue.encode_length]
    omega
  | postOnly inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, PostOnlyValue.encode_length]
    omega
  | expireTime inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, ExpireTimeValue.encode_length]
    omega
  | tradeNow inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, TradeNowValue.encode_length]
    omega
  | handleInst inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, HandleInstValue.encode_length]
    omega
  | bboWeightIndicator inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, BboWeightIndicatorValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega
  | aiqStrategy inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, AiqStrategyValue.encode_length]
    omega
  | aiqGroupId inner =>
    simp only [ReplacedMessageOptionalValue.encode, List.length_append, encodeUInt_length, AiqGroupIdValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ReplacedMessageAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (ReplacedMessageAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : ReplacedMessageAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ReplacedMessageAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ReplacedMessageAppendage

/-- Replaced Message -/
structure ReplacedMessage where
  timestamp : BitVec 64
  origUserRefNum : BitVec 32
  userRefNum : BitVec 32
  side : Side
  quantity : BitVec 32
  symbol : Alpha 8
  price : BitVec 64
  timeInForce : TimeInForce
  display : Display
  orderReferenceNumber : BitVec 64
  capacity : Capacity
  interMarketSweepEligibility : InterMarketSweepEligibility
  crossType : CrossType
  orderState : OrderState
  clordid : Alpha 14
  replacedMessageAppendage : Sized 2 ReplacedMessageAppendage.encode
  deriving DecidableEq, Repr

namespace ReplacedMessage

def encode (message : ReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.origUserRefNum
    ++ (encodeUInt 4 message.userRefNum
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.price
    ++ (TimeInForce.encode message.timeInForce
    ++ (Display.encode message.display
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Capacity.encode message.capacity
    ++ (InterMarketSweepEligibility.encode message.interMarketSweepEligibility
    ++ (CrossType.encode message.crossType
    ++ (OrderState.encode message.orderState
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany ReplacedMessageAppendage.encode message.replacedMessageAppendage.val).length)
    ++ (encodeMany ReplacedMessageAppendage.encode message.replacedMessageAppendage.val))))))))))))))))

def decode (bytes : List UInt8) : Option (ReplacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (origUserRefNum, bytes) ← decodeUInt 4 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (display, bytes) ← Display.decode bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (interMarketSweepEligibility, bytes) ← InterMarketSweepEligibility.decode bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (clordid, bytes) ← Alpha.decode 14 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (replacedMessageAppendage_, bytes) ← decodeSized ReplacedMessageAppendage.decode appendageLength.toNat bytes
  if fits_replacedMessageAppendage : (encodeMany ReplacedMessageAppendage.encode replacedMessageAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, origUserRefNum, userRefNum, side, quantity, symbol, price, timeInForce, display, orderReferenceNumber, capacity, interMarketSweepEligibility, crossType, orderState, clordid, replacedMessageAppendage := ⟨replacedMessageAppendage_, fits_replacedMessageAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReplacedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReplacedMessage) : (encode message).length ≤ 65602 := by
  have bound_replacedMessageAppendage := message.replacedMessageAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Side.encode_length, Alpha.encode_length, TimeInForce.encode_length, Display.encode_length, Capacity.encode_length, InterMarketSweepEligibility.encode_length, CrossType.encode_length, OrderState.encode_length]
  omega

@[simp] theorem decode_encode (message : ReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InterMarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 ReplacedMessageAppendage.encode ReplacedMessageAppendage.decode ReplacedMessageAppendage.decode_encode ReplacedMessageAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.replacedMessageAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReplacedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReplacedMessage

/-- Any Canceled Message Optional Value, selected by Canceled Message Optional Field -/
inductive CanceledMessageOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace CanceledMessageOptionalValue

/-- The Canceled Message Optional Field each message is sent under -/
def tag : CanceledMessageOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : CanceledMessageOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CanceledMessageOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CanceledMessageOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : CanceledMessageOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CanceledMessageOptionalValue

/-- Canceled Message Appendage -/
structure CanceledMessageAppendage where
  canceledMessageOptionalValue : CanceledMessageOptionalValue
  deriving DecidableEq, Repr

namespace CanceledMessageAppendage

def encodeBody (message : CanceledMessageAppendage) : List UInt8 :=
  encodeUInt 1 (CanceledMessageOptionalValue.tag message.canceledMessageOptionalValue)
    ++ (CanceledMessageOptionalValue.encode message.canceledMessageOptionalValue)

def decodeBody (bytes : List UInt8) : Option (CanceledMessageAppendage × List UInt8) := do
  let (canceledMessageOptionalField, bytes) ← decodeUInt 1 bytes
  let (canceledMessageOptionalValue, bytes) ← CanceledMessageOptionalValue.decode canceledMessageOptionalField bytes
  pure ({ canceledMessageOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : CanceledMessageAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CanceledMessageOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : CanceledMessageAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.canceledMessageOptionalValue with
  | userRefIdx inner =>
    simp only [CanceledMessageOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : CanceledMessageAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (CanceledMessageAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : CanceledMessageAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : CanceledMessageAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end CanceledMessageAppendage

/-- Canceled Message -/
structure CanceledMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  quantity : BitVec 32
  cancelOrderReason : CancelOrderReason
  canceledMessageAppendage : Option (Sized 2 CanceledMessageAppendage.encode)
  deriving DecidableEq, Repr

namespace CanceledMessage

/-- The Canceled Message Appendage when there: its length, then the entries filling it -/
def encodeCanceledMessageAppendage (items : Sized 2 CanceledMessageAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany CanceledMessageAppendage.encode items.val).length) ++ encodeMany CanceledMessageAppendage.encode items.val

def decodeCanceledMessageAppendage (bytes : List UInt8) : Option (Sized 2 CanceledMessageAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized CanceledMessageAppendage.decode length.toNat bytes
  if fits : (encodeMany CanceledMessageAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeCanceledMessageAppendage_encodeCanceledMessageAppendage (items : Sized 2 CanceledMessageAppendage.encode) (rest : List UInt8) :
    decodeCanceledMessageAppendage (encodeCanceledMessageAppendage items ++ rest) = some (items, rest) := by
  unfold decodeCanceledMessageAppendage encodeCanceledMessageAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 CanceledMessageAppendage.encode CanceledMessageAppendage.decode CanceledMessageAppendage.decode_encode CanceledMessageAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeCanceledMessageAppendage_length_pos (items : Sized 2 CanceledMessageAppendage.encode) : (encodeCanceledMessageAppendage items).length > 0 := by
  unfold encodeCanceledMessageAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : CanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.quantity
    ++ (CancelOrderReason.encode message.cancelOrderReason
    ++ (encodeTail encodeCanceledMessageAppendage message.canceledMessageAppendage))))

def decode (bytes : List UInt8) : Option CanceledMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (cancelOrderReason, bytes) ← CancelOrderReason.decode bytes
  let canceledMessageAppendage ← decodeTail decodeCanceledMessageAppendage bytes
  pure { timestamp, userRefNum, quantity, cancelOrderReason, canceledMessageAppendage }

theorem encode_length_pos (message : CanceledMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : CanceledMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CancelOrderReason.decode_encode, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeCanceledMessageAppendage decodeCanceledMessageAppendage decodeCanceledMessageAppendage_encodeCanceledMessageAppendage encodeCanceledMessageAppendage_length_pos, some_bind]
  rfl

end CanceledMessage

/-- Any Aiq Canceled Optional Value, selected by Aiq Canceled Optional Field -/
inductive AiqCanceledOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace AiqCanceledOptionalValue

/-- The Aiq Canceled Optional Field each message is sent under -/
def tag : AiqCanceledOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : AiqCanceledOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AiqCanceledOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AiqCanceledOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : AiqCanceledOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AiqCanceledOptionalValue

/-- Aiq Canceled Appendage -/
structure AiqCanceledAppendage where
  aiqCanceledOptionalValue : AiqCanceledOptionalValue
  deriving DecidableEq, Repr

namespace AiqCanceledAppendage

def encodeBody (message : AiqCanceledAppendage) : List UInt8 :=
  encodeUInt 1 (AiqCanceledOptionalValue.tag message.aiqCanceledOptionalValue)
    ++ (AiqCanceledOptionalValue.encode message.aiqCanceledOptionalValue)

def decodeBody (bytes : List UInt8) : Option (AiqCanceledAppendage × List UInt8) := do
  let (aiqCanceledOptionalField, bytes) ← decodeUInt 1 bytes
  let (aiqCanceledOptionalValue, bytes) ← AiqCanceledOptionalValue.decode aiqCanceledOptionalField bytes
  pure ({ aiqCanceledOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : AiqCanceledAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AiqCanceledOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : AiqCanceledAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.aiqCanceledOptionalValue with
  | userRefIdx inner =>
    simp only [AiqCanceledOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : AiqCanceledAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (AiqCanceledAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : AiqCanceledAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : AiqCanceledAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end AiqCanceledAppendage

/-- Aiq Canceled Message -/
structure AiqCanceledMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  decrementShares : BitVec 32
  orderCancelReason : Alpha 1
  quantityPreventedFromTrading : BitVec 32
  executionPrice : BitVec 64
  liquidityFlag : LiquidityFlag
  aiqStrategy : AiqStrategy
  aiqCanceledAppendage : Option (Sized 2 AiqCanceledAppendage.encode)
  deriving DecidableEq, Repr

namespace AiqCanceledMessage

/-- The Aiq Canceled Appendage when there: its length, then the entries filling it -/
def encodeAiqCanceledAppendage (items : Sized 2 AiqCanceledAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany AiqCanceledAppendage.encode items.val).length) ++ encodeMany AiqCanceledAppendage.encode items.val

def decodeAiqCanceledAppendage (bytes : List UInt8) : Option (Sized 2 AiqCanceledAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized AiqCanceledAppendage.decode length.toNat bytes
  if fits : (encodeMany AiqCanceledAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeAiqCanceledAppendage_encodeAiqCanceledAppendage (items : Sized 2 AiqCanceledAppendage.encode) (rest : List UInt8) :
    decodeAiqCanceledAppendage (encodeAiqCanceledAppendage items ++ rest) = some (items, rest) := by
  unfold decodeAiqCanceledAppendage encodeAiqCanceledAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 AiqCanceledAppendage.encode AiqCanceledAppendage.decode AiqCanceledAppendage.decode_encode AiqCanceledAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeAiqCanceledAppendage_length_pos (items : Sized 2 AiqCanceledAppendage.encode) : (encodeAiqCanceledAppendage items).length > 0 := by
  unfold encodeAiqCanceledAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : AiqCanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.decrementShares
    ++ (Alpha.encode message.orderCancelReason
    ++ (encodeUInt 4 message.quantityPreventedFromTrading
    ++ (encodeUInt 8 message.executionPrice
    ++ (LiquidityFlag.encode message.liquidityFlag
    ++ (AiqStrategy.encode message.aiqStrategy
    ++ (encodeTail encodeAiqCanceledAppendage message.aiqCanceledAppendage))))))))

def decode (bytes : List UInt8) : Option AiqCanceledMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (decrementShares, bytes) ← decodeUInt 4 bytes
  let (orderCancelReason, bytes) ← Alpha.decode 1 bytes
  let (quantityPreventedFromTrading, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 8 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (aiqStrategy, bytes) ← AiqStrategy.decode bytes
  let aiqCanceledAppendage ← decodeTail decodeAiqCanceledAppendage bytes
  pure { timestamp, userRefNum, decrementShares, orderCancelReason, quantityPreventedFromTrading, executionPrice, liquidityFlag, aiqStrategy, aiqCanceledAppendage }

theorem encode_length_pos (message : AiqCanceledMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : AiqCanceledMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LiquidityFlag.decode_encode, some_bind]
  dsimp only
  rw [AiqStrategy.decode_encode, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeAiqCanceledAppendage decodeAiqCanceledAppendage decodeAiqCanceledAppendage_encodeAiqCanceledAppendage encodeAiqCanceledAppendage_length_pos, some_bind]
  rfl

end AiqCanceledMessage

/-- Any Order Executed Optional Value, selected by Order Executed Optional Field -/
inductive OrderExecutedOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace OrderExecutedOptionalValue

/-- The Order Executed Optional Field each message is sent under -/
def tag : OrderExecutedOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : OrderExecutedOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderExecutedOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderExecutedOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : OrderExecutedOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end OrderExecutedOptionalValue

/-- Order Executed Appendage -/
structure OrderExecutedAppendage where
  orderExecutedOptionalValue : OrderExecutedOptionalValue
  deriving DecidableEq, Repr

namespace OrderExecutedAppendage

def encodeBody (message : OrderExecutedAppendage) : List UInt8 :=
  encodeUInt 1 (OrderExecutedOptionalValue.tag message.orderExecutedOptionalValue)
    ++ (OrderExecutedOptionalValue.encode message.orderExecutedOptionalValue)

def decodeBody (bytes : List UInt8) : Option (OrderExecutedAppendage × List UInt8) := do
  let (orderExecutedOptionalField, bytes) ← decodeUInt 1 bytes
  let (orderExecutedOptionalValue, bytes) ← OrderExecutedOptionalValue.decode orderExecutedOptionalField bytes
  pure ({ orderExecutedOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : OrderExecutedAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderExecutedOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OrderExecutedAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.orderExecutedOptionalValue with
  | userRefIdx inner =>
    simp only [OrderExecutedOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : OrderExecutedAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (OrderExecutedAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : OrderExecutedAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OrderExecutedAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end OrderExecutedAppendage

/-- Order Executed Message -/
structure OrderExecutedMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  quantity : BitVec 32
  price : BitVec 64
  liquidityFlag : LiquidityFlag
  matchNumber : BitVec 64
  orderExecutedAppendage : Sized 2 OrderExecutedAppendage.encode
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price
    ++ (LiquidityFlag.encode message.liquidityFlag
    ++ (encodeUInt 8 message.matchNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderExecutedAppendage.encode message.orderExecutedAppendage.val).length)
    ++ (encodeMany OrderExecutedAppendage.encode message.orderExecutedAppendage.val)))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (orderExecutedAppendage_, bytes) ← decodeSized OrderExecutedAppendage.decode appendageLength.toNat bytes
  if fits_orderExecutedAppendage : (encodeMany OrderExecutedAppendage.encode orderExecutedAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, quantity, price, liquidityFlag, matchNumber, orderExecutedAppendage := ⟨orderExecutedAppendage_, fits_orderExecutedAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecutedMessage) : (encode message).length ≤ 65570 := by
  have bound_orderExecutedAppendage := message.orderExecutedAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, LiquidityFlag.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 OrderExecutedAppendage.encode OrderExecutedAppendage.decode OrderExecutedAppendage.decode_encode OrderExecutedAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.orderExecutedAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecutedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderExecutedMessage

/-- Any Broken Trade Optional Value, selected by Broken Trade Optional Field -/
inductive BrokenTradeOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace BrokenTradeOptionalValue

/-- The Broken Trade Optional Field each message is sent under -/
def tag : BrokenTradeOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : BrokenTradeOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : BrokenTradeOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (BrokenTradeOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : BrokenTradeOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end BrokenTradeOptionalValue

/-- Broken Trade Appendage -/
structure BrokenTradeAppendage where
  brokenTradeOptionalValue : BrokenTradeOptionalValue
  deriving DecidableEq, Repr

namespace BrokenTradeAppendage

def encodeBody (message : BrokenTradeAppendage) : List UInt8 :=
  encodeUInt 1 (BrokenTradeOptionalValue.tag message.brokenTradeOptionalValue)
    ++ (BrokenTradeOptionalValue.encode message.brokenTradeOptionalValue)

def decodeBody (bytes : List UInt8) : Option (BrokenTradeAppendage × List UInt8) := do
  let (brokenTradeOptionalField, bytes) ← decodeUInt 1 bytes
  let (brokenTradeOptionalValue, bytes) ← BrokenTradeOptionalValue.decode brokenTradeOptionalField bytes
  pure ({ brokenTradeOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : BrokenTradeAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BrokenTradeOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : BrokenTradeAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.brokenTradeOptionalValue with
  | userRefIdx inner =>
    simp only [BrokenTradeOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : BrokenTradeAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (BrokenTradeAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : BrokenTradeAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : BrokenTradeAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end BrokenTradeAppendage

/-- Broken Trade Message -/
structure BrokenTradeMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  matchNumber : BitVec 64
  brokenTradeReason : BrokenTradeReason
  clordid : Alpha 14
  brokenTradeAppendage : Option (Sized 2 BrokenTradeAppendage.encode)
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

/-- The Broken Trade Appendage when there: its length, then the entries filling it -/
def encodeBrokenTradeAppendage (items : Sized 2 BrokenTradeAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany BrokenTradeAppendage.encode items.val).length) ++ encodeMany BrokenTradeAppendage.encode items.val

def decodeBrokenTradeAppendage (bytes : List UInt8) : Option (Sized 2 BrokenTradeAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized BrokenTradeAppendage.decode length.toNat bytes
  if fits : (encodeMany BrokenTradeAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeBrokenTradeAppendage_encodeBrokenTradeAppendage (items : Sized 2 BrokenTradeAppendage.encode) (rest : List UInt8) :
    decodeBrokenTradeAppendage (encodeBrokenTradeAppendage items ++ rest) = some (items, rest) := by
  unfold decodeBrokenTradeAppendage encodeBrokenTradeAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 BrokenTradeAppendage.encode BrokenTradeAppendage.decode BrokenTradeAppendage.decode_encode BrokenTradeAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeBrokenTradeAppendage_length_pos (items : Sized 2 BrokenTradeAppendage.encode) : (encodeBrokenTradeAppendage items).length > 0 := by
  unfold encodeBrokenTradeAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 8 message.matchNumber
    ++ (BrokenTradeReason.encode message.brokenTradeReason
    ++ (Alpha.encode message.clordid
    ++ (encodeTail encodeBrokenTradeAppendage message.brokenTradeAppendage)))))

def decode (bytes : List UInt8) : Option BrokenTradeMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (brokenTradeReason, bytes) ← BrokenTradeReason.decode bytes
  let (clordid, bytes) ← Alpha.decode 14 bytes
  let brokenTradeAppendage ← decodeTail decodeBrokenTradeAppendage bytes
  pure { timestamp, userRefNum, matchNumber, brokenTradeReason, clordid, brokenTradeAppendage }

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : BrokenTradeMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BrokenTradeReason.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeBrokenTradeAppendage decodeBrokenTradeAppendage decodeBrokenTradeAppendage_encodeBrokenTradeAppendage encodeBrokenTradeAppendage_length_pos, some_bind]
  rfl

end BrokenTradeMessage

/-- Any Rejected Order Optional Value, selected by Rejected Order Optional Field -/
inductive RejectedOrderOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace RejectedOrderOptionalValue

/-- The Rejected Order Optional Field each message is sent under -/
def tag : RejectedOrderOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : RejectedOrderOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : RejectedOrderOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (RejectedOrderOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : RejectedOrderOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end RejectedOrderOptionalValue

/-- Rejected Order Appendage -/
structure RejectedOrderAppendage where
  rejectedOrderOptionalValue : RejectedOrderOptionalValue
  deriving DecidableEq, Repr

namespace RejectedOrderAppendage

def encodeBody (message : RejectedOrderAppendage) : List UInt8 :=
  encodeUInt 1 (RejectedOrderOptionalValue.tag message.rejectedOrderOptionalValue)
    ++ (RejectedOrderOptionalValue.encode message.rejectedOrderOptionalValue)

def decodeBody (bytes : List UInt8) : Option (RejectedOrderAppendage × List UInt8) := do
  let (rejectedOrderOptionalField, bytes) ← decodeUInt 1 bytes
  let (rejectedOrderOptionalValue, bytes) ← RejectedOrderOptionalValue.decode rejectedOrderOptionalField bytes
  pure ({ rejectedOrderOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : RejectedOrderAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [RejectedOrderOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : RejectedOrderAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.rejectedOrderOptionalValue with
  | userRefIdx inner =>
    simp only [RejectedOrderOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : RejectedOrderAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (RejectedOrderAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : RejectedOrderAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : RejectedOrderAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end RejectedOrderAppendage

/-- Rejected Order Message -/
structure RejectedOrderMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  rejectedOrderReason : BitVec 16
  clordid : Alpha 14
  rejectedOrderAppendage : Option (Sized 2 RejectedOrderAppendage.encode)
  deriving DecidableEq, Repr

namespace RejectedOrderMessage

/-- The Rejected Order Appendage when there: its length, then the entries filling it -/
def encodeRejectedOrderAppendage (items : Sized 2 RejectedOrderAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany RejectedOrderAppendage.encode items.val).length) ++ encodeMany RejectedOrderAppendage.encode items.val

def decodeRejectedOrderAppendage (bytes : List UInt8) : Option (Sized 2 RejectedOrderAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized RejectedOrderAppendage.decode length.toNat bytes
  if fits : (encodeMany RejectedOrderAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeRejectedOrderAppendage_encodeRejectedOrderAppendage (items : Sized 2 RejectedOrderAppendage.encode) (rest : List UInt8) :
    decodeRejectedOrderAppendage (encodeRejectedOrderAppendage items ++ rest) = some (items, rest) := by
  unfold decodeRejectedOrderAppendage encodeRejectedOrderAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 RejectedOrderAppendage.encode RejectedOrderAppendage.decode RejectedOrderAppendage.decode_encode RejectedOrderAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeRejectedOrderAppendage_length_pos (items : Sized 2 RejectedOrderAppendage.encode) : (encodeRejectedOrderAppendage items).length > 0 := by
  unfold encodeRejectedOrderAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : RejectedOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 2 message.rejectedOrderReason
    ++ (Alpha.encode message.clordid
    ++ (encodeTail encodeRejectedOrderAppendage message.rejectedOrderAppendage))))

def decode (bytes : List UInt8) : Option RejectedOrderMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (rejectedOrderReason, bytes) ← decodeUInt 2 bytes
  let (clordid, bytes) ← Alpha.decode 14 bytes
  let rejectedOrderAppendage ← decodeTail decodeRejectedOrderAppendage bytes
  pure { timestamp, userRefNum, rejectedOrderReason, clordid, rejectedOrderAppendage }

theorem encode_length_pos (message : RejectedOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : RejectedOrderMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeRejectedOrderAppendage decodeRejectedOrderAppendage decodeRejectedOrderAppendage_encodeRejectedOrderAppendage encodeRejectedOrderAppendage_length_pos, some_bind]
  rfl

end RejectedOrderMessage

/-- Any Cancel Pending Optional Value, selected by Cancel Pending Optional Field -/
inductive CancelPendingOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace CancelPendingOptionalValue

/-- The Cancel Pending Optional Field each message is sent under -/
def tag : CancelPendingOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : CancelPendingOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CancelPendingOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CancelPendingOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : CancelPendingOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CancelPendingOptionalValue

/-- Cancel Pending Appendage -/
structure CancelPendingAppendage where
  cancelPendingOptionalValue : CancelPendingOptionalValue
  deriving DecidableEq, Repr

namespace CancelPendingAppendage

def encodeBody (message : CancelPendingAppendage) : List UInt8 :=
  encodeUInt 1 (CancelPendingOptionalValue.tag message.cancelPendingOptionalValue)
    ++ (CancelPendingOptionalValue.encode message.cancelPendingOptionalValue)

def decodeBody (bytes : List UInt8) : Option (CancelPendingAppendage × List UInt8) := do
  let (cancelPendingOptionalField, bytes) ← decodeUInt 1 bytes
  let (cancelPendingOptionalValue, bytes) ← CancelPendingOptionalValue.decode cancelPendingOptionalField bytes
  pure ({ cancelPendingOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : CancelPendingAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CancelPendingOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : CancelPendingAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.cancelPendingOptionalValue with
  | userRefIdx inner =>
    simp only [CancelPendingOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : CancelPendingAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (CancelPendingAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : CancelPendingAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : CancelPendingAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end CancelPendingAppendage

/-- Cancel Pending Message -/
structure CancelPendingMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  cancelPendingAppendage : Option (Sized 2 CancelPendingAppendage.encode)
  deriving DecidableEq, Repr

namespace CancelPendingMessage

/-- The Cancel Pending Appendage when there: its length, then the entries filling it -/
def encodeCancelPendingAppendage (items : Sized 2 CancelPendingAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany CancelPendingAppendage.encode items.val).length) ++ encodeMany CancelPendingAppendage.encode items.val

def decodeCancelPendingAppendage (bytes : List UInt8) : Option (Sized 2 CancelPendingAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized CancelPendingAppendage.decode length.toNat bytes
  if fits : (encodeMany CancelPendingAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeCancelPendingAppendage_encodeCancelPendingAppendage (items : Sized 2 CancelPendingAppendage.encode) (rest : List UInt8) :
    decodeCancelPendingAppendage (encodeCancelPendingAppendage items ++ rest) = some (items, rest) := by
  unfold decodeCancelPendingAppendage encodeCancelPendingAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 CancelPendingAppendage.encode CancelPendingAppendage.decode CancelPendingAppendage.decode_encode CancelPendingAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeCancelPendingAppendage_length_pos (items : Sized 2 CancelPendingAppendage.encode) : (encodeCancelPendingAppendage items).length > 0 := by
  unfold encodeCancelPendingAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : CancelPendingMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeTail encodeCancelPendingAppendage message.cancelPendingAppendage))

def decode (bytes : List UInt8) : Option CancelPendingMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let cancelPendingAppendage ← decodeTail decodeCancelPendingAppendage bytes
  pure { timestamp, userRefNum, cancelPendingAppendage }

theorem encode_length_pos (message : CancelPendingMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : CancelPendingMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeCancelPendingAppendage decodeCancelPendingAppendage decodeCancelPendingAppendage_encodeCancelPendingAppendage encodeCancelPendingAppendage_length_pos, some_bind]
  rfl

end CancelPendingMessage

/-- Any Cancel Reject Optional Value, selected by Cancel Reject Optional Field -/
inductive CancelRejectOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace CancelRejectOptionalValue

/-- The Cancel Reject Optional Field each message is sent under -/
def tag : CancelRejectOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : CancelRejectOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CancelRejectOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CancelRejectOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : CancelRejectOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CancelRejectOptionalValue

/-- Cancel Reject Appendage -/
structure CancelRejectAppendage where
  cancelRejectOptionalValue : CancelRejectOptionalValue
  deriving DecidableEq, Repr

namespace CancelRejectAppendage

def encodeBody (message : CancelRejectAppendage) : List UInt8 :=
  encodeUInt 1 (CancelRejectOptionalValue.tag message.cancelRejectOptionalValue)
    ++ (CancelRejectOptionalValue.encode message.cancelRejectOptionalValue)

def decodeBody (bytes : List UInt8) : Option (CancelRejectAppendage × List UInt8) := do
  let (cancelRejectOptionalField, bytes) ← decodeUInt 1 bytes
  let (cancelRejectOptionalValue, bytes) ← CancelRejectOptionalValue.decode cancelRejectOptionalField bytes
  pure ({ cancelRejectOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : CancelRejectAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CancelRejectOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : CancelRejectAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.cancelRejectOptionalValue with
  | userRefIdx inner =>
    simp only [CancelRejectOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : CancelRejectAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (CancelRejectAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : CancelRejectAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : CancelRejectAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end CancelRejectAppendage

/-- Cancel Reject Message -/
structure CancelRejectMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  cancelRejectAppendage : Option (Sized 2 CancelRejectAppendage.encode)
  deriving DecidableEq, Repr

namespace CancelRejectMessage

/-- The Cancel Reject Appendage when there: its length, then the entries filling it -/
def encodeCancelRejectAppendage (items : Sized 2 CancelRejectAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany CancelRejectAppendage.encode items.val).length) ++ encodeMany CancelRejectAppendage.encode items.val

def decodeCancelRejectAppendage (bytes : List UInt8) : Option (Sized 2 CancelRejectAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized CancelRejectAppendage.decode length.toNat bytes
  if fits : (encodeMany CancelRejectAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeCancelRejectAppendage_encodeCancelRejectAppendage (items : Sized 2 CancelRejectAppendage.encode) (rest : List UInt8) :
    decodeCancelRejectAppendage (encodeCancelRejectAppendage items ++ rest) = some (items, rest) := by
  unfold decodeCancelRejectAppendage encodeCancelRejectAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 CancelRejectAppendage.encode CancelRejectAppendage.decode CancelRejectAppendage.decode_encode CancelRejectAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeCancelRejectAppendage_length_pos (items : Sized 2 CancelRejectAppendage.encode) : (encodeCancelRejectAppendage items).length > 0 := by
  unfold encodeCancelRejectAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : CancelRejectMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeTail encodeCancelRejectAppendage message.cancelRejectAppendage))

def decode (bytes : List UInt8) : Option CancelRejectMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let cancelRejectAppendage ← decodeTail decodeCancelRejectAppendage bytes
  pure { timestamp, userRefNum, cancelRejectAppendage }

theorem encode_length_pos (message : CancelRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : CancelRejectMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeCancelRejectAppendage decodeCancelRejectAppendage decodeCancelRejectAppendage_encodeCancelRejectAppendage encodeCancelRejectAppendage_length_pos, some_bind]
  rfl

end CancelRejectMessage

/-- Any Order Priority Update Optional Value, selected by Order Priority Update Optional Field -/
inductive OrderPriorityUpdateOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace OrderPriorityUpdateOptionalValue

/-- The Order Priority Update Optional Field each message is sent under -/
def tag : OrderPriorityUpdateOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : OrderPriorityUpdateOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderPriorityUpdateOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderPriorityUpdateOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : OrderPriorityUpdateOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end OrderPriorityUpdateOptionalValue

/-- Order Priority Update Appendage -/
structure OrderPriorityUpdateAppendage where
  orderPriorityUpdateOptionalValue : OrderPriorityUpdateOptionalValue
  deriving DecidableEq, Repr

namespace OrderPriorityUpdateAppendage

def encodeBody (message : OrderPriorityUpdateAppendage) : List UInt8 :=
  encodeUInt 1 (OrderPriorityUpdateOptionalValue.tag message.orderPriorityUpdateOptionalValue)
    ++ (OrderPriorityUpdateOptionalValue.encode message.orderPriorityUpdateOptionalValue)

def decodeBody (bytes : List UInt8) : Option (OrderPriorityUpdateAppendage × List UInt8) := do
  let (orderPriorityUpdateOptionalField, bytes) ← decodeUInt 1 bytes
  let (orderPriorityUpdateOptionalValue, bytes) ← OrderPriorityUpdateOptionalValue.decode orderPriorityUpdateOptionalField bytes
  pure ({ orderPriorityUpdateOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : OrderPriorityUpdateAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderPriorityUpdateOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OrderPriorityUpdateAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.orderPriorityUpdateOptionalValue with
  | userRefIdx inner =>
    simp only [OrderPriorityUpdateOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : OrderPriorityUpdateAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (OrderPriorityUpdateAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : OrderPriorityUpdateAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OrderPriorityUpdateAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end OrderPriorityUpdateAppendage

/-- Order Priority Update Message -/
structure OrderPriorityUpdateMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  price : BitVec 64
  display : Display
  orderReferenceNumber : BitVec 64
  orderPriorityUpdateAppendage : Option (Sized 2 OrderPriorityUpdateAppendage.encode)
  deriving DecidableEq, Repr

namespace OrderPriorityUpdateMessage

/-- The Order Priority Update Appendage when there: its length, then the entries filling it -/
def encodeOrderPriorityUpdateAppendage (items : Sized 2 OrderPriorityUpdateAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderPriorityUpdateAppendage.encode items.val).length) ++ encodeMany OrderPriorityUpdateAppendage.encode items.val

def decodeOrderPriorityUpdateAppendage (bytes : List UInt8) : Option (Sized 2 OrderPriorityUpdateAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized OrderPriorityUpdateAppendage.decode length.toNat bytes
  if fits : (encodeMany OrderPriorityUpdateAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeOrderPriorityUpdateAppendage_encodeOrderPriorityUpdateAppendage (items : Sized 2 OrderPriorityUpdateAppendage.encode) (rest : List UInt8) :
    decodeOrderPriorityUpdateAppendage (encodeOrderPriorityUpdateAppendage items ++ rest) = some (items, rest) := by
  unfold decodeOrderPriorityUpdateAppendage encodeOrderPriorityUpdateAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 OrderPriorityUpdateAppendage.encode OrderPriorityUpdateAppendage.decode OrderPriorityUpdateAppendage.decode_encode OrderPriorityUpdateAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeOrderPriorityUpdateAppendage_length_pos (items : Sized 2 OrderPriorityUpdateAppendage.encode) : (encodeOrderPriorityUpdateAppendage items).length > 0 := by
  unfold encodeOrderPriorityUpdateAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : OrderPriorityUpdateMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 8 message.price
    ++ (Display.encode message.display
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeTail encodeOrderPriorityUpdateAppendage message.orderPriorityUpdateAppendage)))))

def decode (bytes : List UInt8) : Option OrderPriorityUpdateMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (display, bytes) ← Display.decode bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let orderPriorityUpdateAppendage ← decodeTail decodeOrderPriorityUpdateAppendage bytes
  pure { timestamp, userRefNum, price, display, orderReferenceNumber, orderPriorityUpdateAppendage }

theorem encode_length_pos (message : OrderPriorityUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : OrderPriorityUpdateMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Display.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeOrderPriorityUpdateAppendage decodeOrderPriorityUpdateAppendage decodeOrderPriorityUpdateAppendage_encodeOrderPriorityUpdateAppendage encodeOrderPriorityUpdateAppendage_length_pos, some_bind]
  rfl

end OrderPriorityUpdateMessage

/-- Locate Broker: 4 bytes -/
structure LocateBrokerValue where
  locateBroker : Alpha 4
  deriving DecidableEq, Repr

namespace LocateBrokerValue

def encode (message : LocateBrokerValue) : List UInt8 :=
  Alpha.encode message.locateBroker

def decode (bytes : List UInt8) : Option (LocateBrokerValue × List UInt8) := do
  let (locateBroker, bytes) ← Alpha.decode 4 bytes
  pure ({ locateBroker }, bytes)

@[simp] theorem encode_length (message : LocateBrokerValue) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LocateBrokerValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LocateBrokerValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LocateBrokerValue

/-- Any Order Modified Optional Value, selected by Order Modified Optional Field -/
inductive OrderModifiedOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  | sharesLocated (message : SharesLocatedValue) -- 25
  | locateBroker (message : LocateBrokerValue) -- 26
  deriving DecidableEq, Repr

namespace OrderModifiedOptionalValue

/-- The Order Modified Optional Field each message is sent under -/
def tag : OrderModifiedOptionalValue → BitVec 8
  | .userRefIdx _ => 28
  | .sharesLocated _ => 25
  | .locateBroker _ => 26

def encode : OrderModifiedOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message
  | .sharesLocated message => SharesLocatedValue.encode message
  | .locateBroker message => LocateBrokerValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderModifiedOptionalValue) : (encode message).length ≤ 4 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega
  | sharesLocated inner =>
    simp only [encode, SharesLocatedValue.encode_length]
    omega
  | locateBroker inner =>
    simp only [encode, LocateBrokerValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderModifiedOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else if tag = 25 then (SharesLocatedValue.decode bytes).map fun (message, rest) => (.sharesLocated message, rest)
  else if tag = 26 then (LocateBrokerValue.decode bytes).map fun (message, rest) => (.locateBroker message, rest)
  else none

@[simp] theorem decode_encode (message : OrderModifiedOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end OrderModifiedOptionalValue

/-- Order Modified Appendage -/
structure OrderModifiedAppendage where
  orderModifiedOptionalValue : OrderModifiedOptionalValue
  deriving DecidableEq, Repr

namespace OrderModifiedAppendage

def encodeBody (message : OrderModifiedAppendage) : List UInt8 :=
  encodeUInt 1 (OrderModifiedOptionalValue.tag message.orderModifiedOptionalValue)
    ++ (OrderModifiedOptionalValue.encode message.orderModifiedOptionalValue)

def decodeBody (bytes : List UInt8) : Option (OrderModifiedAppendage × List UInt8) := do
  let (orderModifiedOptionalField, bytes) ← decodeUInt 1 bytes
  let (orderModifiedOptionalValue, bytes) ← OrderModifiedOptionalValue.decode orderModifiedOptionalField bytes
  pure ({ orderModifiedOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : OrderModifiedAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderModifiedOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OrderModifiedAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.orderModifiedOptionalValue with
  | userRefIdx inner =>
    simp only [OrderModifiedOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega
  | sharesLocated inner =>
    simp only [OrderModifiedOptionalValue.encode, List.length_append, encodeUInt_length, SharesLocatedValue.encode_length]
    omega
  | locateBroker inner =>
    simp only [OrderModifiedOptionalValue.encode, List.length_append, encodeUInt_length, LocateBrokerValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : OrderModifiedAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (OrderModifiedAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : OrderModifiedAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OrderModifiedAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end OrderModifiedAppendage

/-- Order Modified Message -/
structure OrderModifiedMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  side : Side
  quantity : BitVec 32
  orderModifiedAppendage : Option (Sized 2 OrderModifiedAppendage.encode)
  deriving DecidableEq, Repr

namespace OrderModifiedMessage

/-- The Order Modified Appendage when there: its length, then the entries filling it -/
def encodeOrderModifiedAppendage (items : Sized 2 OrderModifiedAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderModifiedAppendage.encode items.val).length) ++ encodeMany OrderModifiedAppendage.encode items.val

def decodeOrderModifiedAppendage (bytes : List UInt8) : Option (Sized 2 OrderModifiedAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized OrderModifiedAppendage.decode length.toNat bytes
  if fits : (encodeMany OrderModifiedAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeOrderModifiedAppendage_encodeOrderModifiedAppendage (items : Sized 2 OrderModifiedAppendage.encode) (rest : List UInt8) :
    decodeOrderModifiedAppendage (encodeOrderModifiedAppendage items ++ rest) = some (items, rest) := by
  unfold decodeOrderModifiedAppendage encodeOrderModifiedAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 OrderModifiedAppendage.encode OrderModifiedAppendage.decode OrderModifiedAppendage.decode_encode OrderModifiedAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeOrderModifiedAppendage_length_pos (items : Sized 2 OrderModifiedAppendage.encode) : (encodeOrderModifiedAppendage items).length > 0 := by
  unfold encodeOrderModifiedAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : OrderModifiedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity
    ++ (encodeTail encodeOrderModifiedAppendage message.orderModifiedAppendage))))

def decode (bytes : List UInt8) : Option OrderModifiedMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let orderModifiedAppendage ← decodeTail decodeOrderModifiedAppendage bytes
  pure { timestamp, userRefNum, side, quantity, orderModifiedAppendage }

theorem encode_length_pos (message : OrderModifiedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : OrderModifiedMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeOrderModifiedAppendage decodeOrderModifiedAppendage decodeOrderModifiedAppendage_encodeOrderModifiedAppendage encodeOrderModifiedAppendage_length_pos, some_bind]
  rfl

end OrderModifiedMessage

/-- Display Quantity: 4 bytes -/
structure DisplayQuantityValue where
  displayQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace DisplayQuantityValue

def encode (message : DisplayQuantityValue) : List UInt8 :=
  encodeUInt 4 message.displayQuantity

def decode (bytes : List UInt8) : Option (DisplayQuantityValue × List UInt8) := do
  let (displayQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ displayQuantity }, bytes)

@[simp] theorem encode_length (message : DisplayQuantityValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DisplayQuantityValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisplayQuantityValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisplayQuantityValue

/-- Display Price: 8 bytes -/
structure DisplayPriceValue where
  displayPrice : BitVec 64
  deriving DecidableEq, Repr

namespace DisplayPriceValue

def encode (message : DisplayPriceValue) : List UInt8 :=
  encodeUInt 8 message.displayPrice

def decode (bytes : List UInt8) : Option (DisplayPriceValue × List UInt8) := do
  let (displayPrice, bytes) ← decodeUInt 8 bytes
  pure ({ displayPrice }, bytes)

@[simp] theorem encode_length (message : DisplayPriceValue) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DisplayPriceValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisplayPriceValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisplayPriceValue

/-- Secondary Ord Ref Num: 8 bytes -/
structure SecondaryOrdRefNumValue where
  secondaryOrdRefNum : BitVec 64
  deriving DecidableEq, Repr

namespace SecondaryOrdRefNumValue

def encode (message : SecondaryOrdRefNumValue) : List UInt8 :=
  encodeUInt 8 message.secondaryOrdRefNum

def decode (bytes : List UInt8) : Option (SecondaryOrdRefNumValue × List UInt8) := do
  let (secondaryOrdRefNum, bytes) ← decodeUInt 8 bytes
  pure ({ secondaryOrdRefNum }, bytes)

@[simp] theorem encode_length (message : SecondaryOrdRefNumValue) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondaryOrdRefNumValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondaryOrdRefNumValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondaryOrdRefNumValue

/-- Any Order Restated Optional Value, selected by Order Restated Optional Field -/
inductive OrderRestatedOptionalValue where
  | displayQuantity (message : DisplayQuantityValue) -- 22
  | displayPrice (message : DisplayPriceValue) -- 23
  | secondaryOrdRefNum (message : SecondaryOrdRefNumValue) -- 1
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace OrderRestatedOptionalValue

/-- The Order Restated Optional Field each message is sent under -/
def tag : OrderRestatedOptionalValue → BitVec 8
  | .displayQuantity _ => 22
  | .displayPrice _ => 23
  | .secondaryOrdRefNum _ => 1
  | .userRefIdx _ => 28

def encode : OrderRestatedOptionalValue → List UInt8
  | .displayQuantity message => DisplayQuantityValue.encode message
  | .displayPrice message => DisplayPriceValue.encode message
  | .secondaryOrdRefNum message => SecondaryOrdRefNumValue.encode message
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderRestatedOptionalValue) : (encode message).length ≤ 8 := by
  cases message with
  | displayQuantity inner =>
    simp only [encode, DisplayQuantityValue.encode_length]
    omega
  | displayPrice inner =>
    simp only [encode, DisplayPriceValue.encode_length]
    omega
  | secondaryOrdRefNum inner =>
    simp only [encode, SecondaryOrdRefNumValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderRestatedOptionalValue × List UInt8) :=
  if tag = 22 then (DisplayQuantityValue.decode bytes).map fun (message, rest) => (.displayQuantity message, rest)
  else if tag = 23 then (DisplayPriceValue.decode bytes).map fun (message, rest) => (.displayPrice message, rest)
  else if tag = 1 then (SecondaryOrdRefNumValue.decode bytes).map fun (message, rest) => (.secondaryOrdRefNum message, rest)
  else if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : OrderRestatedOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end OrderRestatedOptionalValue

/-- Order Restated Appendage -/
structure OrderRestatedAppendage where
  orderRestatedOptionalValue : OrderRestatedOptionalValue
  deriving DecidableEq, Repr

namespace OrderRestatedAppendage

def encodeBody (message : OrderRestatedAppendage) : List UInt8 :=
  encodeUInt 1 (OrderRestatedOptionalValue.tag message.orderRestatedOptionalValue)
    ++ (OrderRestatedOptionalValue.encode message.orderRestatedOptionalValue)

def decodeBody (bytes : List UInt8) : Option (OrderRestatedAppendage × List UInt8) := do
  let (orderRestatedOptionalField, bytes) ← decodeUInt 1 bytes
  let (orderRestatedOptionalValue, bytes) ← OrderRestatedOptionalValue.decode orderRestatedOptionalField bytes
  pure ({ orderRestatedOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : OrderRestatedAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderRestatedOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OrderRestatedAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.orderRestatedOptionalValue with
  | displayQuantity inner =>
    simp only [OrderRestatedOptionalValue.encode, List.length_append, encodeUInt_length, DisplayQuantityValue.encode_length]
    omega
  | displayPrice inner =>
    simp only [OrderRestatedOptionalValue.encode, List.length_append, encodeUInt_length, DisplayPriceValue.encode_length]
    omega
  | secondaryOrdRefNum inner =>
    simp only [OrderRestatedOptionalValue.encode, List.length_append, encodeUInt_length, SecondaryOrdRefNumValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [OrderRestatedOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : OrderRestatedAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (OrderRestatedAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : OrderRestatedAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OrderRestatedAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end OrderRestatedAppendage

/-- Order Restated Message -/
structure OrderRestatedMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  orderRestatedReason : OrderRestatedReason
  orderRestatedAppendage : Sized 2 OrderRestatedAppendage.encode
  deriving DecidableEq, Repr

namespace OrderRestatedMessage

def encode (message : OrderRestatedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (OrderRestatedReason.encode message.orderRestatedReason
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderRestatedAppendage.encode message.orderRestatedAppendage.val).length)
    ++ (encodeMany OrderRestatedAppendage.encode message.orderRestatedAppendage.val))))

def decode (bytes : List UInt8) : Option (OrderRestatedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderRestatedReason, bytes) ← OrderRestatedReason.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (orderRestatedAppendage_, bytes) ← decodeSized OrderRestatedAppendage.decode appendageLength.toNat bytes
  if fits_orderRestatedAppendage : (encodeMany OrderRestatedAppendage.encode orderRestatedAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, orderRestatedReason, orderRestatedAppendage := ⟨orderRestatedAppendage_, fits_orderRestatedAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderRestatedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderRestatedMessage) : (encode message).length ≤ 65550 := by
  have bound_orderRestatedAppendage := message.orderRestatedAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderRestatedReason.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderRestatedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderRestatedReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 OrderRestatedAppendage.encode OrderRestatedAppendage.decode OrderRestatedAppendage.decode_encode OrderRestatedAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.orderRestatedAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderRestatedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderRestatedMessage

/-- Any Account Query Response Optional Value, selected by Account Query Response Optional Field -/
inductive AccountQueryResponseOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace AccountQueryResponseOptionalValue

/-- The Account Query Response Optional Field each message is sent under -/
def tag : AccountQueryResponseOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : AccountQueryResponseOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AccountQueryResponseOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AccountQueryResponseOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : AccountQueryResponseOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AccountQueryResponseOptionalValue

/-- Account Query Response Appendage -/
structure AccountQueryResponseAppendage where
  accountQueryResponseOptionalValue : AccountQueryResponseOptionalValue
  deriving DecidableEq, Repr

namespace AccountQueryResponseAppendage

def encodeBody (message : AccountQueryResponseAppendage) : List UInt8 :=
  encodeUInt 1 (AccountQueryResponseOptionalValue.tag message.accountQueryResponseOptionalValue)
    ++ (AccountQueryResponseOptionalValue.encode message.accountQueryResponseOptionalValue)

def decodeBody (bytes : List UInt8) : Option (AccountQueryResponseAppendage × List UInt8) := do
  let (accountQueryResponseOptionalField, bytes) ← decodeUInt 1 bytes
  let (accountQueryResponseOptionalValue, bytes) ← AccountQueryResponseOptionalValue.decode accountQueryResponseOptionalField bytes
  pure ({ accountQueryResponseOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : AccountQueryResponseAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AccountQueryResponseOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : AccountQueryResponseAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.accountQueryResponseOptionalValue with
  | userRefIdx inner =>
    simp only [AccountQueryResponseOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : AccountQueryResponseAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (AccountQueryResponseAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : AccountQueryResponseAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : AccountQueryResponseAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end AccountQueryResponseAppendage

/-- Account Query Response Message -/
structure AccountQueryResponseMessage where
  timestamp : BitVec 64
  nextUserRefNum : BitVec 32
  accountQueryResponseAppendage : Option (Sized 2 AccountQueryResponseAppendage.encode)
  deriving DecidableEq, Repr

namespace AccountQueryResponseMessage

/-- The Account Query Response Appendage when there: its length, then the entries filling it -/
def encodeAccountQueryResponseAppendage (items : Sized 2 AccountQueryResponseAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany AccountQueryResponseAppendage.encode items.val).length) ++ encodeMany AccountQueryResponseAppendage.encode items.val

def decodeAccountQueryResponseAppendage (bytes : List UInt8) : Option (Sized 2 AccountQueryResponseAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized AccountQueryResponseAppendage.decode length.toNat bytes
  if fits : (encodeMany AccountQueryResponseAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeAccountQueryResponseAppendage_encodeAccountQueryResponseAppendage (items : Sized 2 AccountQueryResponseAppendage.encode) (rest : List UInt8) :
    decodeAccountQueryResponseAppendage (encodeAccountQueryResponseAppendage items ++ rest) = some (items, rest) := by
  unfold decodeAccountQueryResponseAppendage encodeAccountQueryResponseAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 AccountQueryResponseAppendage.encode AccountQueryResponseAppendage.decode AccountQueryResponseAppendage.decode_encode AccountQueryResponseAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeAccountQueryResponseAppendage_length_pos (items : Sized 2 AccountQueryResponseAppendage.encode) : (encodeAccountQueryResponseAppendage items).length > 0 := by
  unfold encodeAccountQueryResponseAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : AccountQueryResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.nextUserRefNum
    ++ (encodeTail encodeAccountQueryResponseAppendage message.accountQueryResponseAppendage))

def decode (bytes : List UInt8) : Option AccountQueryResponseMessage := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (nextUserRefNum, bytes) ← decodeUInt 4 bytes
  let accountQueryResponseAppendage ← decodeTail decodeAccountQueryResponseAppendage bytes
  pure { timestamp, nextUserRefNum, accountQueryResponseAppendage }

theorem encode_length_pos (message : AccountQueryResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : AccountQueryResponseMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeTail_encodeTail encodeAccountQueryResponseAppendage decodeAccountQueryResponseAppendage decodeAccountQueryResponseAppendage_encodeAccountQueryResponseAppendage encodeAccountQueryResponseAppendage_length_pos, some_bind]
  rfl

end AccountQueryResponseMessage

/-- Side: 1 bytes -/
structure SideValue where
  side : Side
  deriving DecidableEq, Repr

namespace SideValue

def encode (message : SideValue) : List UInt8 :=
  Side.encode message.side

def decode (bytes : List UInt8) : Option (SideValue × List UInt8) := do
  let (side, bytes) ← Side.decode bytes
  pure ({ side }, bytes)

@[simp] theorem encode_length (message : SideValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Side.encode_length]

theorem encode_length_pos (message : SideValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SideValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Side.decode_encode, some_bind]
  rfl

end SideValue

/-- Any Mass Cancel Response Optional Value, selected by Mass Cancel Response Optional Field -/
inductive MassCancelResponseOptionalValue where
  | side (message : SideValue) -- 27
  | groupId (message : GroupIdValue) -- 24
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace MassCancelResponseOptionalValue

/-- The Mass Cancel Response Optional Field each message is sent under -/
def tag : MassCancelResponseOptionalValue → BitVec 8
  | .side _ => 27
  | .groupId _ => 24
  | .userRefIdx _ => 28

def encode : MassCancelResponseOptionalValue → List UInt8
  | .side message => SideValue.encode message
  | .groupId message => GroupIdValue.encode message
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MassCancelResponseOptionalValue) : (encode message).length ≤ 2 := by
  cases message with
  | side inner =>
    simp only [encode, SideValue.encode_length]
    omega
  | groupId inner =>
    simp only [encode, GroupIdValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MassCancelResponseOptionalValue × List UInt8) :=
  if tag = 27 then (SideValue.decode bytes).map fun (message, rest) => (.side message, rest)
  else if tag = 24 then (GroupIdValue.decode bytes).map fun (message, rest) => (.groupId message, rest)
  else if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : MassCancelResponseOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MassCancelResponseOptionalValue

/-- Mass Cancel Response Appendage -/
structure MassCancelResponseAppendage where
  massCancelResponseOptionalValue : MassCancelResponseOptionalValue
  deriving DecidableEq, Repr

namespace MassCancelResponseAppendage

def encodeBody (message : MassCancelResponseAppendage) : List UInt8 :=
  encodeUInt 1 (MassCancelResponseOptionalValue.tag message.massCancelResponseOptionalValue)
    ++ (MassCancelResponseOptionalValue.encode message.massCancelResponseOptionalValue)

def decodeBody (bytes : List UInt8) : Option (MassCancelResponseAppendage × List UInt8) := do
  let (massCancelResponseOptionalField, bytes) ← decodeUInt 1 bytes
  let (massCancelResponseOptionalValue, bytes) ← MassCancelResponseOptionalValue.decode massCancelResponseOptionalField bytes
  pure ({ massCancelResponseOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : MassCancelResponseAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MassCancelResponseOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MassCancelResponseAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.massCancelResponseOptionalValue with
  | side inner =>
    simp only [MassCancelResponseOptionalValue.encode, List.length_append, encodeUInt_length, SideValue.encode_length]
    omega
  | groupId inner =>
    simp only [MassCancelResponseOptionalValue.encode, List.length_append, encodeUInt_length, GroupIdValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [MassCancelResponseOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : MassCancelResponseAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (MassCancelResponseAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : MassCancelResponseAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : MassCancelResponseAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end MassCancelResponseAppendage

/-- Mass Cancel Response Message -/
structure MassCancelResponseMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  firm : Alpha 4
  symbol : Alpha 8
  massCancelResponseAppendage : Sized 2 MassCancelResponseAppendage.encode
  deriving DecidableEq, Repr

namespace MassCancelResponseMessage

def encode (message : MassCancelResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany MassCancelResponseAppendage.encode message.massCancelResponseAppendage.val).length)
    ++ (encodeMany MassCancelResponseAppendage.encode message.massCancelResponseAppendage.val)))))

def decode (bytes : List UInt8) : Option (MassCancelResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (massCancelResponseAppendage_, bytes) ← decodeSized MassCancelResponseAppendage.decode appendageLength.toNat bytes
  if fits_massCancelResponseAppendage : (encodeMany MassCancelResponseAppendage.encode massCancelResponseAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, firm, symbol, massCancelResponseAppendage := ⟨massCancelResponseAppendage_, fits_massCancelResponseAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassCancelResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassCancelResponseMessage) : (encode message).length ≤ 65561 := by
  have bound_massCancelResponseAppendage := message.massCancelResponseAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MassCancelResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 MassCancelResponseAppendage.encode MassCancelResponseAppendage.decode MassCancelResponseAppendage.decode_encode MassCancelResponseAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.massCancelResponseAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MassCancelResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MassCancelResponseMessage

/-- Any Disable Order Entry Response Optional Value, selected by Disable Order Entry Response Optional Field -/
inductive DisableOrderEntryResponseOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace DisableOrderEntryResponseOptionalValue

/-- The Disable Order Entry Response Optional Field each message is sent under -/
def tag : DisableOrderEntryResponseOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : DisableOrderEntryResponseOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : DisableOrderEntryResponseOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (DisableOrderEntryResponseOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : DisableOrderEntryResponseOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end DisableOrderEntryResponseOptionalValue

/-- Disable Order Entry Response Appendage -/
structure DisableOrderEntryResponseAppendage where
  disableOrderEntryResponseOptionalValue : DisableOrderEntryResponseOptionalValue
  deriving DecidableEq, Repr

namespace DisableOrderEntryResponseAppendage

def encodeBody (message : DisableOrderEntryResponseAppendage) : List UInt8 :=
  encodeUInt 1 (DisableOrderEntryResponseOptionalValue.tag message.disableOrderEntryResponseOptionalValue)
    ++ (DisableOrderEntryResponseOptionalValue.encode message.disableOrderEntryResponseOptionalValue)

def decodeBody (bytes : List UInt8) : Option (DisableOrderEntryResponseAppendage × List UInt8) := do
  let (disableOrderEntryResponseOptionalField, bytes) ← decodeUInt 1 bytes
  let (disableOrderEntryResponseOptionalValue, bytes) ← DisableOrderEntryResponseOptionalValue.decode disableOrderEntryResponseOptionalField bytes
  pure ({ disableOrderEntryResponseOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : DisableOrderEntryResponseAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [DisableOrderEntryResponseOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : DisableOrderEntryResponseAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.disableOrderEntryResponseOptionalValue with
  | userRefIdx inner =>
    simp only [DisableOrderEntryResponseOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : DisableOrderEntryResponseAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (DisableOrderEntryResponseAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : DisableOrderEntryResponseAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : DisableOrderEntryResponseAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end DisableOrderEntryResponseAppendage

/-- Disable Order Entry Response Message -/
structure DisableOrderEntryResponseMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  firm : Alpha 4
  disableOrderEntryResponseAppendage : Sized 2 DisableOrderEntryResponseAppendage.encode
  deriving DecidableEq, Repr

namespace DisableOrderEntryResponseMessage

def encode (message : DisableOrderEntryResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.firm
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany DisableOrderEntryResponseAppendage.encode message.disableOrderEntryResponseAppendage.val).length)
    ++ (encodeMany DisableOrderEntryResponseAppendage.encode message.disableOrderEntryResponseAppendage.val))))

def decode (bytes : List UInt8) : Option (DisableOrderEntryResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (disableOrderEntryResponseAppendage_, bytes) ← decodeSized DisableOrderEntryResponseAppendage.decode appendageLength.toNat bytes
  if fits_disableOrderEntryResponseAppendage : (encodeMany DisableOrderEntryResponseAppendage.encode disableOrderEntryResponseAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, firm, disableOrderEntryResponseAppendage := ⟨disableOrderEntryResponseAppendage_, fits_disableOrderEntryResponseAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : DisableOrderEntryResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DisableOrderEntryResponseMessage) : (encode message).length ≤ 65553 := by
  have bound_disableOrderEntryResponseAppendage := message.disableOrderEntryResponseAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : DisableOrderEntryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 DisableOrderEntryResponseAppendage.encode DisableOrderEntryResponseAppendage.decode DisableOrderEntryResponseAppendage.decode_encode DisableOrderEntryResponseAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.disableOrderEntryResponseAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DisableOrderEntryResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DisableOrderEntryResponseMessage

/-- Any Enable Order Entry Response Optional Value, selected by Enable Order Entry Response Optional Field -/
inductive EnableOrderEntryResponseOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace EnableOrderEntryResponseOptionalValue

/-- The Enable Order Entry Response Optional Field each message is sent under -/
def tag : EnableOrderEntryResponseOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : EnableOrderEntryResponseOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EnableOrderEntryResponseOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (EnableOrderEntryResponseOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : EnableOrderEntryResponseOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end EnableOrderEntryResponseOptionalValue

/-- Enable Order Entry Response Appendage -/
structure EnableOrderEntryResponseAppendage where
  enableOrderEntryResponseOptionalValue : EnableOrderEntryResponseOptionalValue
  deriving DecidableEq, Repr

namespace EnableOrderEntryResponseAppendage

def encodeBody (message : EnableOrderEntryResponseAppendage) : List UInt8 :=
  encodeUInt 1 (EnableOrderEntryResponseOptionalValue.tag message.enableOrderEntryResponseOptionalValue)
    ++ (EnableOrderEntryResponseOptionalValue.encode message.enableOrderEntryResponseOptionalValue)

def decodeBody (bytes : List UInt8) : Option (EnableOrderEntryResponseAppendage × List UInt8) := do
  let (enableOrderEntryResponseOptionalField, bytes) ← decodeUInt 1 bytes
  let (enableOrderEntryResponseOptionalValue, bytes) ← EnableOrderEntryResponseOptionalValue.decode enableOrderEntryResponseOptionalField bytes
  pure ({ enableOrderEntryResponseOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : EnableOrderEntryResponseAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EnableOrderEntryResponseOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : EnableOrderEntryResponseAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.enableOrderEntryResponseOptionalValue with
  | userRefIdx inner =>
    simp only [EnableOrderEntryResponseOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : EnableOrderEntryResponseAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (EnableOrderEntryResponseAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : EnableOrderEntryResponseAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : EnableOrderEntryResponseAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end EnableOrderEntryResponseAppendage

/-- Enable Order Entry Response Message -/
structure EnableOrderEntryResponseMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  firm : Alpha 4
  enableOrderEntryResponseAppendage : Sized 2 EnableOrderEntryResponseAppendage.encode
  deriving DecidableEq, Repr

namespace EnableOrderEntryResponseMessage

def encode (message : EnableOrderEntryResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.firm
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany EnableOrderEntryResponseAppendage.encode message.enableOrderEntryResponseAppendage.val).length)
    ++ (encodeMany EnableOrderEntryResponseAppendage.encode message.enableOrderEntryResponseAppendage.val))))

def decode (bytes : List UInt8) : Option (EnableOrderEntryResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (enableOrderEntryResponseAppendage_, bytes) ← decodeSized EnableOrderEntryResponseAppendage.decode appendageLength.toNat bytes
  if fits_enableOrderEntryResponseAppendage : (encodeMany EnableOrderEntryResponseAppendage.encode enableOrderEntryResponseAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, firm, enableOrderEntryResponseAppendage := ⟨enableOrderEntryResponseAppendage_, fits_enableOrderEntryResponseAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : EnableOrderEntryResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnableOrderEntryResponseMessage) : (encode message).length ≤ 65553 := by
  have bound_enableOrderEntryResponseAppendage := message.enableOrderEntryResponseAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : EnableOrderEntryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 EnableOrderEntryResponseAppendage.encode EnableOrderEntryResponseAppendage.decode EnableOrderEntryResponseAppendage.decode_encode EnableOrderEntryResponseAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.enableOrderEntryResponseAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EnableOrderEntryResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EnableOrderEntryResponseMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderAcceptedMessage (message : OrderAcceptedMessage) -- "A" 0x41
  | replacedMessage (message : ReplacedMessage) -- "U" 0x55
  | canceledMessage (message : CanceledMessage) -- "C" 0x43
  | aiqCanceledMessage (message : AiqCanceledMessage) -- "D" 0x44
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | rejectedOrderMessage (message : RejectedOrderMessage) -- "J" 0x4A
  | cancelPendingMessage (message : CancelPendingMessage) -- "P" 0x50
  | cancelRejectMessage (message : CancelRejectMessage) -- "I" 0x49
  | orderPriorityUpdateMessage (message : OrderPriorityUpdateMessage) -- "T" 0x54
  | orderModifiedMessage (message : OrderModifiedMessage) -- "M" 0x4D
  | orderRestatedMessage (message : OrderRestatedMessage) -- "R" 0x52
  | accountQueryResponseMessage (message : AccountQueryResponseMessage) -- "Q" 0x51
  | massCancelResponseMessage (message : MassCancelResponseMessage) -- "X" 0x58
  | disableOrderEntryResponseMessage (message : DisableOrderEntryResponseMessage) -- "G" 0x47
  | enableOrderEntryResponseMessage (message : EnableOrderEntryResponseMessage) -- "K" 0x4B
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .orderAcceptedMessage _ => 65
  | .replacedMessage _ => 85
  | .canceledMessage _ => 67
  | .aiqCanceledMessage _ => 68
  | .orderExecutedMessage _ => 69
  | .brokenTradeMessage _ => 66
  | .rejectedOrderMessage _ => 74
  | .cancelPendingMessage _ => 80
  | .cancelRejectMessage _ => 73
  | .orderPriorityUpdateMessage _ => 84
  | .orderModifiedMessage _ => 77
  | .orderRestatedMessage _ => 82
  | .accountQueryResponseMessage _ => 81
  | .massCancelResponseMessage _ => 88
  | .disableOrderEntryResponseMessage _ => 71
  | .enableOrderEntryResponseMessage _ => 75

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderAcceptedMessage message => OrderAcceptedMessage.encode message
  | .replacedMessage message => ReplacedMessage.encode message
  | .canceledMessage message => CanceledMessage.encode message
  | .aiqCanceledMessage message => AiqCanceledMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .rejectedOrderMessage message => RejectedOrderMessage.encode message
  | .cancelPendingMessage message => CancelPendingMessage.encode message
  | .cancelRejectMessage message => CancelRejectMessage.encode message
  | .orderPriorityUpdateMessage message => OrderPriorityUpdateMessage.encode message
  | .orderModifiedMessage message => OrderModifiedMessage.encode message
  | .orderRestatedMessage message => OrderRestatedMessage.encode message
  | .accountQueryResponseMessage message => AccountQueryResponseMessage.encode message
  | .massCancelResponseMessage message => MassCancelResponseMessage.encode message
  | .disableOrderEntryResponseMessage message => DisableOrderEntryResponseMessage.encode message
  | .enableOrderEntryResponseMessage message => EnableOrderEntryResponseMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option SequencedMessage :=
  if tag = 83 then (SystemEventMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.systemEventMessage message) else none
  else if tag = 65 then (OrderAcceptedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderAcceptedMessage message) else none
  else if tag = 85 then (ReplacedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.replacedMessage message) else none
  else if tag = 67 then (CanceledMessage.decode bytes).map fun message => .canceledMessage message
  else if tag = 68 then (AiqCanceledMessage.decode bytes).map fun message => .aiqCanceledMessage message
  else if tag = 69 then (OrderExecutedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecutedMessage message) else none
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun message => .brokenTradeMessage message
  else if tag = 74 then (RejectedOrderMessage.decode bytes).map fun message => .rejectedOrderMessage message
  else if tag = 80 then (CancelPendingMessage.decode bytes).map fun message => .cancelPendingMessage message
  else if tag = 73 then (CancelRejectMessage.decode bytes).map fun message => .cancelRejectMessage message
  else if tag = 84 then (OrderPriorityUpdateMessage.decode bytes).map fun message => .orderPriorityUpdateMessage message
  else if tag = 77 then (OrderModifiedMessage.decode bytes).map fun message => .orderModifiedMessage message
  else if tag = 82 then (OrderRestatedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderRestatedMessage message) else none
  else if tag = 81 then (AccountQueryResponseMessage.decode bytes).map fun message => .accountQueryResponseMessage message
  else if tag = 88 then (MassCancelResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.massCancelResponseMessage message) else none
  else if tag = 71 then (DisableOrderEntryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.disableOrderEntryResponseMessage message) else none
  else if tag = 75 then (EnableOrderEntryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.enableOrderEntryResponseMessage message) else none
  else none

theorem decode_encode (message : SequencedMessage) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | systemEventMessage message => simp [decode, encode, tag, SystemEventMessage.decode_encode_nil]
  | orderAcceptedMessage message => simp [decode, encode, tag, OrderAcceptedMessage.decode_encode_nil]
  | replacedMessage message => simp [decode, encode, tag, ReplacedMessage.decode_encode_nil]
  | canceledMessage message => simp [decode, encode, tag, CanceledMessage.decode_encode]
  | aiqCanceledMessage message => simp [decode, encode, tag, AiqCanceledMessage.decode_encode]
  | orderExecutedMessage message => simp [decode, encode, tag, OrderExecutedMessage.decode_encode_nil]
  | brokenTradeMessage message => simp [decode, encode, tag, BrokenTradeMessage.decode_encode]
  | rejectedOrderMessage message => simp [decode, encode, tag, RejectedOrderMessage.decode_encode]
  | cancelPendingMessage message => simp [decode, encode, tag, CancelPendingMessage.decode_encode]
  | cancelRejectMessage message => simp [decode, encode, tag, CancelRejectMessage.decode_encode]
  | orderPriorityUpdateMessage message => simp [decode, encode, tag, OrderPriorityUpdateMessage.decode_encode]
  | orderModifiedMessage message => simp [decode, encode, tag, OrderModifiedMessage.decode_encode]
  | orderRestatedMessage message => simp [decode, encode, tag, OrderRestatedMessage.decode_encode_nil]
  | accountQueryResponseMessage message => simp [decode, encode, tag, AccountQueryResponseMessage.decode_encode]
  | massCancelResponseMessage message => simp [decode, encode, tag, MassCancelResponseMessage.decode_encode_nil]
  | disableOrderEntryResponseMessage message => simp [decode, encode, tag, DisableOrderEntryResponseMessage.decode_encode_nil]
  | enableOrderEntryResponseMessage message => simp [decode, encode, tag, EnableOrderEntryResponseMessage.decode_encode_nil]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option SequencedDataPacket := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let sequencedMessage ← SequencedMessage.decode sequencedMessageType bytes
  pure { sequencedMessage }

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

theorem decode_encode (message : SequencedDataPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | endOfSession (message : EndOfSession) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession : ServerPayload → Bool
  | .endOfSession _ => true
  | _ => false

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedPacket message) else none
  else if tag = 74 then (LoginRejectedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedPacket message) else none
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun message => .sequencedDataPacket message
  else if tag = 72 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 90 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginAcceptedPacket message => simp [decode, encode, tag, LoginAcceptedPacket.decode_encode_nil]
  | loginRejectedPacket message => simp [decode, encode, tag, LoginRejectedPacket.decode_encode_nil]
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]

end ServerPayload

/-- Server Soup Bin Tcp Packet: the body, which the record carries with the proof it fits its frame -/
structure ServerSoupBinTcpPacketBody where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacketBody

def encodeBody (message : ServerSoupBinTcpPacketBody) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerSoupBinTcpPacketBody := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let serverPayload ← ServerPayload.decode serverPacketType bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacketBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession (message : ServerSoupBinTcpPacketBody) : Bool :=
  ServerPayload.endsSession message.serverPayload

end ServerSoupBinTcpPacketBody

/-- Server Soup Bin Tcp Packet: the body with the proof its encoding fits Packet Length, whose 2 bytes no bound of the fields fits -/
abbrev ServerSoupBinTcpPacket := Fitting ServerSoupBinTcpPacketBody.encodeBody 0 65536

namespace ServerSoupBinTcpPacket

def encode (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeFramed 2 0 ServerSoupBinTcpPacketBody.encodeBody message.val

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFittingAll 2 0 ServerSoupBinTcpPacketBody.encodeBody ServerSoupBinTcpPacketBody.decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAll_encodeFramed 2 0 ServerSoupBinTcpPacketBody.encodeBody ServerSoupBinTcpPacketBody.decodeBody message (ServerSoupBinTcpPacketBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ServerSoupBinTcpPacket) : (encode message).length ≤ 65537 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramed_length]
  omega

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession (message : ServerSoupBinTcpPacket) : Bool :=
  ServerSoupBinTcpPacketBody.endsSession message.val

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  serverSoupBinTcpPacket_last : endsLast ServerSoupBinTcpPacket.endsSession serverSoupBinTcpPacket = true
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  if last_serverSoupBinTcpPacket : endsLast ServerSoupBinTcpPacket.endsSession serverSoupBinTcpPacket = true then
    pure { serverSoupBinTcpPacket, serverSoupBinTcpPacket_last := last_serverSoupBinTcpPacket }
  else none

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rw [dite_eq_left message.serverSoupBinTcpPacket_last]
  rfl

end ServerPacket

end Omi.NasdaqNsmequitiesOrdersOuchV50Server
