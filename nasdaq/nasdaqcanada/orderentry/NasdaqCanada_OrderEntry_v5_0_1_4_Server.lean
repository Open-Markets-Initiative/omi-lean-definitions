import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nasdaq Canada Order Entry v5.0.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Appendage Length and the Account Query Response Appendage it sizes are there only when bytes remain after Account Query Response Message's fixed fields: they are read as one optional closing field.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Server Soup Bin Tcp Packet's body has no bound its 2 byte Packet Length must fit, so every message carries the proof its own encoding fits: the record is its body with that proof, checked as the frame is read.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNasdaqcanadaOrderentryOuchV5014Server

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

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x35]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | sellShort -- Sell Short
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .sellShort => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else .sellShort

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | sellShort => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x30, 0x33, 0x36, 0x38, 0x50]

inductive TimeInForce where
  | day -- Day
  | immediateOrCancel -- Immediate Or Cancel
  | goodTillDate -- Good Till Date
  | streamOrKill -- Stream Or Kill
  | postOnlyOrder -- Post Only Order
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .day => 0x30
  | .immediateOrCancel => 0x33
  | .goodTillDate => 0x36
  | .streamOrKill => 0x38
  | .postOnlyOrder => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x30 then .day
  else if byte = 0x33 then .immediateOrCancel
  else if byte = 0x36 then .goodTillDate
  else if byte = 0x38 then .streamOrKill
  else .postOnlyOrder

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | immediateOrCancel => decide
  | goodTillDate => decide
  | streamOrKill => decide
  | postOnlyOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Ex Destination: one byte code -/
def ExDestination.codes : List UInt8 :=
  [0x43, 0x32, 0x44, 0x53]

inductive ExDestination where
  | cxc -- Cxc
  | cx2 -- Cx 2
  | cxd -- Cxd
  | smartOrderRouter -- Smart Order Router
  | unlisted (byte : { byte : UInt8 // byte ∉ ExDestination.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExDestination

def toByte : ExDestination → UInt8
  | .cxc => 0x43
  | .cx2 => 0x32
  | .cxd => 0x44
  | .smartOrderRouter => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExDestination :=
  if byte = 0x43 then .cxc
  else if byte = 0x32 then .cx2
  else if byte = 0x44 then .cxd
  else .smartOrderRouter

def ofByte (byte : UInt8) : ExDestination :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExDestination) : ofByte value.toByte = value := by
  cases value with
  | cxc => decide
  | cx2 => decide
  | cxd => decide
  | smartOrderRouter => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExDestination) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExDestination × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExDestination) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExDestination) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExDestination

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

@[simp] theorem decode_encode (value : OrderState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderState

/-- Peg Type: one byte code -/
def PegType.codes : List UInt8 :=
  [0x4D, 0x52, 0x78, 0x53, 0x4C, 0x6F]

inductive PegType where
  | midpointPeg -- Midpoint Peg
  | primaryPeg -- Primary Peg
  | minimumPriceImprovement -- Minimum Price Improvement
  | seekPriceImprovement -- Seek Price Improvement
  | melo -- Melo
  | oddLotLiquidityProviding -- Odd Lot Liquidity Providing
  | unlisted (byte : { byte : UInt8 // byte ∉ PegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PegType

def toByte : PegType → UInt8
  | .midpointPeg => 0x4D
  | .primaryPeg => 0x52
  | .minimumPriceImprovement => 0x78
  | .seekPriceImprovement => 0x53
  | .melo => 0x4C
  | .oddLotLiquidityProviding => 0x6F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PegType :=
  if byte = 0x4D then .midpointPeg
  else if byte = 0x52 then .primaryPeg
  else if byte = 0x78 then .minimumPriceImprovement
  else if byte = 0x53 then .seekPriceImprovement
  else if byte = 0x4C then .melo
  else .oddLotLiquidityProviding

def ofByte (byte : UInt8) : PegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PegType) : ofByte value.toByte = value := by
  cases value with
  | midpointPeg => decide
  | primaryPeg => decide
  | minimumPriceImprovement => decide
  | seekPriceImprovement => decide
  | melo => decide
  | oddLotLiquidityProviding => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PegType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PegType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PegType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PegType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PegType

/-- Min Qty Type: one byte code -/
def MinQtyType.codes : List UInt8 :=
  [0x4E, 0x6D, 0x74, 0x7A]

inductive MinQtyType where
  | maq -- Maq
  | maqAtTouch -- Maq At Touch
  | mqAtTouch -- Mq At Touch
  | minimumQuantity -- Minimum Quantity
  | unlisted (byte : { byte : UInt8 // byte ∉ MinQtyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MinQtyType

def toByte : MinQtyType → UInt8
  | .maq => 0x4E
  | .maqAtTouch => 0x6D
  | .mqAtTouch => 0x74
  | .minimumQuantity => 0x7A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MinQtyType :=
  if byte = 0x4E then .maq
  else if byte = 0x6D then .maqAtTouch
  else if byte = 0x74 then .mqAtTouch
  else .minimumQuantity

def ofByte (byte : UInt8) : MinQtyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MinQtyType) : ofByte value.toByte = value := by
  cases value with
  | maq => decide
  | maqAtTouch => decide
  | mqAtTouch => decide
  | minimumQuantity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MinQtyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MinQtyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MinQtyType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MinQtyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MinQtyType

/-- Order Origination: one byte code -/
def OrderOrigination.codes : List UInt8 :=
  [0x35, 0x36, 0x37]

inductive OrderOrigination where
  | directAccessCustomer -- Direct Access Customer
  | foreignDealerEquivalent -- Foreign Dealer Equivalent
  | executiononlyService -- Executiononly Service
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderOrigination.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderOrigination

def toByte : OrderOrigination → UInt8
  | .directAccessCustomer => 0x35
  | .foreignDealerEquivalent => 0x36
  | .executiononlyService => 0x37
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderOrigination :=
  if byte = 0x35 then .directAccessCustomer
  else if byte = 0x36 then .foreignDealerEquivalent
  else .executiononlyService

def ofByte (byte : UInt8) : OrderOrigination :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderOrigination) : ofByte value.toByte = value := by
  cases value with
  | directAccessCustomer => decide
  | foreignDealerEquivalent => decide
  | executiononlyService => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderOrigination) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderOrigination × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderOrigination) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderOrigination) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderOrigination

/-- Routing Arrangement Indicator: one byte code -/
def RoutingArrangementIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive RoutingArrangementIndicator where
  | noRoutingArrangementInPlace -- No Routing Arrangement In Place
  | routingArrangementInPlace -- Routing Arrangement In Place
  | unlisted (byte : { byte : UInt8 // byte ∉ RoutingArrangementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoutingArrangementIndicator

def toByte : RoutingArrangementIndicator → UInt8
  | .noRoutingArrangementInPlace => 0x30
  | .routingArrangementInPlace => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoutingArrangementIndicator :=
  if byte = 0x30 then .noRoutingArrangementInPlace
  else .routingArrangementInPlace

def ofByte (byte : UInt8) : RoutingArrangementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoutingArrangementIndicator) : ofByte value.toByte = value := by
  cases value with
  | noRoutingArrangementInPlace => decide
  | routingArrangementInPlace => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RoutingArrangementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RoutingArrangementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RoutingArrangementIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RoutingArrangementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RoutingArrangementIndicator

/-- Basket Trade: one byte code -/
def BasketTrade.codes : List UInt8 :=
  [0x4E, 0x59]

inductive BasketTrade where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ BasketTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BasketTrade

def toByte : BasketTrade → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BasketTrade :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : BasketTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BasketTrade) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BasketTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BasketTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BasketTrade) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BasketTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BasketTrade

/-- Program Trade: one byte code -/
def ProgramTrade.codes : List UInt8 :=
  [0x4E, 0x59]

inductive ProgramTrade where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ ProgramTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProgramTrade

def toByte : ProgramTrade → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProgramTrade :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : ProgramTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProgramTrade) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProgramTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProgramTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProgramTrade) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ProgramTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProgramTrade

/-- Gef Eligible: one byte code -/
def GefEligible.codes : List UInt8 :=
  [0x4E, 0x59]

inductive GefEligible where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ GefEligible.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GefEligible

def toByte : GefEligible → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GefEligible :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : GefEligible :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GefEligible) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GefEligible) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GefEligible × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GefEligible) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : GefEligible) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GefEligible

/-- Anonymous: one byte code -/
def Anonymous.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Anonymous where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ Anonymous.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Anonymous

def toByte : Anonymous → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Anonymous :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : Anonymous :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Anonymous) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Anonymous) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Anonymous × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Anonymous) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Anonymous) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Anonymous

/-- Bypass: one byte code -/
def Bypass.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Bypass where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ Bypass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Bypass

def toByte : Bypass → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Bypass :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : Bypass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Bypass) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Bypass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Bypass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Bypass) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Bypass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Bypass

/-- Tsxncib: one byte code -/
def Tsxncib.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Tsxncib where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ Tsxncib.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tsxncib

def toByte : Tsxncib → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tsxncib :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : Tsxncib :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tsxncib) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tsxncib) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tsxncib × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tsxncib) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tsxncib) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tsxncib

/-- No Trade Feat: one byte code -/
def NoTradeFeat.codes : List UInt8 :=
  [0x4E, 0x4F, 0x44, 0x45]

inductive NoTradeFeat where
  | cancelNewest -- Cancel Newest
  | cancelOldest -- Cancel Oldest
  | decrementAndCancel -- Decrement And Cancel
  | executeTrade -- Execute Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ NoTradeFeat.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NoTradeFeat

def toByte : NoTradeFeat → UInt8
  | .cancelNewest => 0x4E
  | .cancelOldest => 0x4F
  | .decrementAndCancel => 0x44
  | .executeTrade => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NoTradeFeat :=
  if byte = 0x4E then .cancelNewest
  else if byte = 0x4F then .cancelOldest
  else if byte = 0x44 then .decrementAndCancel
  else .executeTrade

def ofByte (byte : UInt8) : NoTradeFeat :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NoTradeFeat) : ofByte value.toByte = value := by
  cases value with
  | cancelNewest => decide
  | cancelOldest => decide
  | decrementAndCancel => decide
  | executeTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NoTradeFeat) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NoTradeFeat × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NoTradeFeat) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NoTradeFeat) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NoTradeFeat

/-- Short Marking Exempt: one byte code -/
def ShortMarkingExempt.codes : List UInt8 :=
  [0x30]

inductive ShortMarkingExempt where
  | sme -- Sme
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortMarkingExempt.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortMarkingExempt

def toByte : ShortMarkingExempt → UInt8
  | .sme => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ShortMarkingExempt :=
  .sme

def ofByte (byte : UInt8) : ShortMarkingExempt :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortMarkingExempt) : ofByte value.toByte = value := by
  cases value with
  | sme => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortMarkingExempt) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortMarkingExempt × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortMarkingExempt) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortMarkingExempt) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortMarkingExempt

/-- Conditional Order: one byte code -/
def ConditionalOrder.codes : List UInt8 :=
  [0x43, 0x58]

inductive ConditionalOrder where
  | conditionalOrder -- Conditional Order
  | extendedFirmupTimeConditionalOrder -- Extended Firmup Time Conditional Order
  | unlisted (byte : { byte : UInt8 // byte ∉ ConditionalOrder.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ConditionalOrder

def toByte : ConditionalOrder → UInt8
  | .conditionalOrder => 0x43
  | .extendedFirmupTimeConditionalOrder => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ConditionalOrder :=
  if byte = 0x43 then .conditionalOrder
  else .extendedFirmupTimeConditionalOrder

def ofByte (byte : UInt8) : ConditionalOrder :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ConditionalOrder) : ofByte value.toByte = value := by
  cases value with
  | conditionalOrder => decide
  | extendedFirmupTimeConditionalOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ConditionalOrder) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ConditionalOrder × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ConditionalOrder) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ConditionalOrder) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ConditionalOrder

/-- Allow Conditional: one byte code -/
def AllowConditional.codes : List UInt8 :=
  [0x4E, 0x59]

inductive AllowConditional where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ AllowConditional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllowConditional

def toByte : AllowConditional → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AllowConditional :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : AllowConditional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllowConditional) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllowConditional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllowConditional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllowConditional) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllowConditional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllowConditional

/-- Cxd Connect: one byte code -/
def CxdConnect.codes : List UInt8 :=
  [0x4E, 0x59]

inductive CxdConnect where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ CxdConnect.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CxdConnect

def toByte : CxdConnect → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CxdConnect :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : CxdConnect :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CxdConnect) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CxdConnect) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CxdConnect × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CxdConnect) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CxdConnect) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CxdConnect

/-- Pure Stream Connect: one byte code -/
def PureStreamConnect.codes : List UInt8 :=
  [0x4E, 0x59]

inductive PureStreamConnect where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ PureStreamConnect.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PureStreamConnect

def toByte : PureStreamConnect → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PureStreamConnect :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : PureStreamConnect :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PureStreamConnect) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PureStreamConnect) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PureStreamConnect × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PureStreamConnect) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PureStreamConnect) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PureStreamConnect

/-- Handl Inst: one byte code -/
def HandlInst.codes : List UInt8 :=
  [0x66, 0x31, 0x35]

inductive HandlInst where
  | dao -- Dao
  | oprReprice -- Opr Reprice
  | oprCancel -- Opr Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ HandlInst.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HandlInst

def toByte : HandlInst → UInt8
  | .dao => 0x66
  | .oprReprice => 0x31
  | .oprCancel => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HandlInst :=
  if byte = 0x66 then .dao
  else if byte = 0x31 then .oprReprice
  else .oprCancel

def ofByte (byte : UInt8) : HandlInst :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HandlInst) : ofByte value.toByte = value := by
  cases value with
  | dao => decide
  | oprReprice => decide
  | oprCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HandlInst) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HandlInst × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HandlInst) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HandlInst) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HandlInst

/-- Nbbo Setter: one byte code -/
def NbboSetter.codes : List UInt8 :=
  [0x59]

inductive NbboSetter where
  | nbboSetter -- Nbbo Setter
  | unlisted (byte : { byte : UInt8 // byte ∉ NbboSetter.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NbboSetter

def toByte : NbboSetter → UInt8
  | .nbboSetter => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : NbboSetter :=
  .nbboSetter

def ofByte (byte : UInt8) : NbboSetter :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NbboSetter) : ofByte value.toByte = value := by
  cases value with
  | nbboSetter => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NbboSetter) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NbboSetter × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NbboSetter) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NbboSetter) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NbboSetter

/-- Liquidity Flag: one byte code -/
def LiquidityFlag.codes : List UInt8 :=
  [0x41, 0x52, 0x61, 0x72, 0x64, 0x44, 0x67, 0x47, 0x43, 0x53, 0x4F, 0x45, 0x4C, 0x50, 0x4D, 0x46]

inductive LiquidityFlag where
  | orderAddedLiquidity -- Order Added Liquidity
  | orderRemovedLiquidity -- Order Removed Liquidity
  | orderAddedHiddenLiquidity -- Order Added Hidden Liquidity
  | orderRemovedHiddenLiquidity -- Order Removed Hidden Liquidity
  | orderAddedHiddenLiquidityAtthetouch -- Order Added Hidden Liquidity Atthetouch
  | orderRemovedHiddenLiquidityAtthetouch -- Order Removed Hidden Liquidity Atthetouch
  | orderAddedGefLiquidity -- Order Added Gef Liquidity
  | orderRemovedGefLiquidity -- Order Removed Gef Liquidity
  | marketOnClose -- Market On Close
  | displayedLiquidityaddingOrderImprovesTheNbbo -- Displayed Liquidityadding Order Improves The Nbbo
  | openingClosingAuction -- Opening Closing Auction
  | lastSaleTradingSession -- Last Sale Trading Session
  | melo -- Melo
  | cxdPureStreamRatebasedExecution -- Cxd Pure Stream Ratebased Execution
  | cxdPureStreamLsMidpointBlockRemovedLiquidity -- Cxd Pure Stream Ls Midpoint Block Removed Liquidity
  | xft -- Xft
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityFlag

def toByte : LiquidityFlag → UInt8
  | .orderAddedLiquidity => 0x41
  | .orderRemovedLiquidity => 0x52
  | .orderAddedHiddenLiquidity => 0x61
  | .orderRemovedHiddenLiquidity => 0x72
  | .orderAddedHiddenLiquidityAtthetouch => 0x64
  | .orderRemovedHiddenLiquidityAtthetouch => 0x44
  | .orderAddedGefLiquidity => 0x67
  | .orderRemovedGefLiquidity => 0x47
  | .marketOnClose => 0x43
  | .displayedLiquidityaddingOrderImprovesTheNbbo => 0x53
  | .openingClosingAuction => 0x4F
  | .lastSaleTradingSession => 0x45
  | .melo => 0x4C
  | .cxdPureStreamRatebasedExecution => 0x50
  | .cxdPureStreamLsMidpointBlockRemovedLiquidity => 0x4D
  | .xft => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityFlag :=
  if byte = 0x41 then .orderAddedLiquidity
  else if byte = 0x52 then .orderRemovedLiquidity
  else if byte = 0x61 then .orderAddedHiddenLiquidity
  else if byte = 0x72 then .orderRemovedHiddenLiquidity
  else if byte = 0x64 then .orderAddedHiddenLiquidityAtthetouch
  else if byte = 0x44 then .orderRemovedHiddenLiquidityAtthetouch
  else if byte = 0x67 then .orderAddedGefLiquidity
  else if byte = 0x47 then .orderRemovedGefLiquidity
  else if byte = 0x43 then .marketOnClose
  else if byte = 0x53 then .displayedLiquidityaddingOrderImprovesTheNbbo
  else if byte = 0x4F then .openingClosingAuction
  else if byte = 0x45 then .lastSaleTradingSession
  else if byte = 0x4C then .melo
  else if byte = 0x50 then .cxdPureStreamRatebasedExecution
  else if byte = 0x4D then .cxdPureStreamLsMidpointBlockRemovedLiquidity
  else .xft

def ofByte (byte : UInt8) : LiquidityFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityFlag) : ofByte value.toByte = value := by
  cases value with
  | orderAddedLiquidity => decide
  | orderRemovedLiquidity => decide
  | orderAddedHiddenLiquidity => decide
  | orderRemovedHiddenLiquidity => decide
  | orderAddedHiddenLiquidityAtthetouch => decide
  | orderRemovedHiddenLiquidityAtthetouch => decide
  | orderAddedGefLiquidity => decide
  | orderRemovedGefLiquidity => decide
  | marketOnClose => decide
  | displayedLiquidityaddingOrderImprovesTheNbbo => decide
  | openingClosingAuction => decide
  | lastSaleTradingSession => decide
  | melo => decide
  | cxdPureStreamRatebasedExecution => decide
  | cxdPureStreamLsMidpointBlockRemovedLiquidity => decide
  | xft => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityFlag

/-- Exec Broker: one byte code -/
def ExecBroker.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F]

inductive ExecBroker where
  | unspecified -- Unspecified
  | chix -- Chix
  | cx2 -- Cx 2
  | cxd -- Cxd
  | tsx -- Tsx
  | pure -- Pure
  | alph -- Alph
  | match_ -- Match
  | omga -- Omga
  | lynx -- Lynx
  | aeqn -- Aeqn
  | aeql -- Aeql
  | cse2 -- Cse 2
  | alpx -- Alpx
  | alpd -- Alpd
  | icx -- Icx
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecBroker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecBroker

def toByte : ExecBroker → UInt8
  | .unspecified => 0x20
  | .chix => 0x41
  | .cx2 => 0x42
  | .cxd => 0x43
  | .tsx => 0x44
  | .pure => 0x45
  | .alph => 0x46
  | .match_ => 0x47
  | .omga => 0x48
  | .lynx => 0x49
  | .aeqn => 0x4A
  | .aeql => 0x4B
  | .cse2 => 0x4C
  | .alpx => 0x4D
  | .alpd => 0x4E
  | .icx => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecBroker :=
  if byte = 0x20 then .unspecified
  else if byte = 0x41 then .chix
  else if byte = 0x42 then .cx2
  else if byte = 0x43 then .cxd
  else if byte = 0x44 then .tsx
  else if byte = 0x45 then .pure
  else if byte = 0x46 then .alph
  else if byte = 0x47 then .match_
  else if byte = 0x48 then .omga
  else if byte = 0x49 then .lynx
  else if byte = 0x4A then .aeqn
  else if byte = 0x4B then .aeql
  else if byte = 0x4C then .cse2
  else if byte = 0x4D then .alpx
  else if byte = 0x4E then .alpd
  else .icx

def ofByte (byte : UInt8) : ExecBroker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecBroker) : ofByte value.toByte = value := by
  cases value with
  | unspecified => decide
  | chix => decide
  | cx2 => decide
  | cxd => decide
  | tsx => decide
  | pure => decide
  | alph => decide
  | match_ => decide
  | omga => decide
  | lynx => decide
  | aeqn => decide
  | aeql => decide
  | cse2 => decide
  | alpx => decide
  | alpd => decide
  | icx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecBroker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecBroker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecBroker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecBroker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecBroker

/-- Execute Match: one byte code -/
def ExecuteMatch.codes : List UInt8 :=
  [0x4E, 0x59]

inductive ExecuteMatch where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecuteMatch.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecuteMatch

def toByte : ExecuteMatch → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecuteMatch :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : ExecuteMatch :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecuteMatch) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecuteMatch) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecuteMatch × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecuteMatch) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecuteMatch) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecuteMatch

/-- Broker Pref: one byte code -/
def BrokerPref.codes : List UInt8 :=
  [0x4E, 0x59]

inductive BrokerPref where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ BrokerPref.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BrokerPref

def toByte : BrokerPref → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BrokerPref :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : BrokerPref :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BrokerPref) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BrokerPref) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BrokerPref × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BrokerPref) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BrokerPref) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BrokerPref

/-- Principal Trade: one byte code -/
def PrincipalTrade.codes : List UInt8 :=
  [0x4E, 0x59]

inductive PrincipalTrade where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ PrincipalTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrincipalTrade

def toByte : PrincipalTrade → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrincipalTrade :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : PrincipalTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrincipalTrade) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrincipalTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrincipalTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrincipalTrade) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrincipalTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrincipalTrade

/-- Wash Trade: one byte code -/
def WashTrade.codes : List UInt8 :=
  [0x4E, 0x59]

inductive WashTrade where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ WashTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace WashTrade

def toByte : WashTrade → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : WashTrade :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : WashTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : WashTrade) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : WashTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (WashTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : WashTrade) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : WashTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end WashTrade

/-- Restate Reason: one byte code -/
def RestateReason.codes : List UInt8 :=
  [0x4F, 0x58, 0x52]

inductive RestateReason where
  | streamOn -- Stream On
  | streamOff -- Stream Off
  | conditionalOrderFirmupRequest -- Conditional Order Firmup Request
  | unlisted (byte : { byte : UInt8 // byte ∉ RestateReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RestateReason

def toByte : RestateReason → UInt8
  | .streamOn => 0x4F
  | .streamOff => 0x58
  | .conditionalOrderFirmupRequest => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RestateReason :=
  if byte = 0x4F then .streamOn
  else if byte = 0x58 then .streamOff
  else .conditionalOrderFirmupRequest

def ofByte (byte : UInt8) : RestateReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RestateReason) : ofByte value.toByte = value := by
  cases value with
  | streamOn => decide
  | streamOff => decide
  | conditionalOrderFirmupRequest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RestateReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RestateReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RestateReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RestateReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RestateReason

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

/-- Account: 15 bytes -/
structure AccountValue where
  account : Alpha 15
  deriving DecidableEq, Repr

namespace AccountValue

def encode (message : AccountValue) : List UInt8 :=
  Alpha.encode message.account

def decode (bytes : List UInt8) : Option (AccountValue × List UInt8) := do
  let (account, bytes) ← Alpha.decode 15 bytes
  pure ({ account }, bytes)

@[simp] theorem encode_length (message : AccountValue) : (encode message).length = 15 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : AccountValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccountValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end AccountValue

/-- Peg Type: 1 bytes -/
structure PegTypeValue where
  pegType : PegType
  deriving DecidableEq, Repr

namespace PegTypeValue

def encode (message : PegTypeValue) : List UInt8 :=
  PegType.encode message.pegType

def decode (bytes : List UInt8) : Option (PegTypeValue × List UInt8) := do
  let (pegType, bytes) ← PegType.decode bytes
  pure ({ pegType }, bytes)

@[simp] theorem encode_length (message : PegTypeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [PegType.encode_length]

theorem encode_length_pos (message : PegTypeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PegTypeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PegType.decode_encode, some_bind]
  rfl

end PegTypeValue

/-- Min Qty Type: 1 bytes -/
structure MinQtyTypeValue where
  minQtyType : MinQtyType
  deriving DecidableEq, Repr

namespace MinQtyTypeValue

def encode (message : MinQtyTypeValue) : List UInt8 :=
  MinQtyType.encode message.minQtyType

def decode (bytes : List UInt8) : Option (MinQtyTypeValue × List UInt8) := do
  let (minQtyType, bytes) ← MinQtyType.decode bytes
  pure ({ minQtyType }, bytes)

@[simp] theorem encode_length (message : MinQtyTypeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [MinQtyType.encode_length]

theorem encode_length_pos (message : MinQtyTypeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinQtyTypeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MinQtyType.decode_encode, some_bind]
  rfl

end MinQtyTypeValue

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

/-- Peg Offset: 8 bytes -/
structure PegOffsetValue where
  pegOffset : BitVec 64
  deriving DecidableEq, Repr

namespace PegOffsetValue

def encode (message : PegOffsetValue) : List UInt8 :=
  encodeUInt 8 message.pegOffset

def decode (bytes : List UInt8) : Option (PegOffsetValue × List UInt8) := do
  let (pegOffset, bytes) ← decodeUInt 8 bytes
  pure ({ pegOffset }, bytes)

@[simp] theorem encode_length (message : PegOffsetValue) : (encode message).length = 8 := by
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

/-- Target Strategy: 2 bytes -/
structure TargetStrategyValue where
  targetStrategy : BitVec 16
  deriving DecidableEq, Repr

namespace TargetStrategyValue

def encode (message : TargetStrategyValue) : List UInt8 :=
  encodeUInt 2 message.targetStrategy

def decode (bytes : List UInt8) : Option (TargetStrategyValue × List UInt8) := do
  let (targetStrategy, bytes) ← decodeUInt 2 bytes
  pure ({ targetStrategy }, bytes)

@[simp] theorem encode_length (message : TargetStrategyValue) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TargetStrategyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TargetStrategyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TargetStrategyValue

/-- Order Origination: 1 bytes -/
structure OrderOriginationValue where
  orderOrigination : OrderOrigination
  deriving DecidableEq, Repr

namespace OrderOriginationValue

def encode (message : OrderOriginationValue) : List UInt8 :=
  OrderOrigination.encode message.orderOrigination

def decode (bytes : List UInt8) : Option (OrderOriginationValue × List UInt8) := do
  let (orderOrigination, bytes) ← OrderOrigination.decode bytes
  pure ({ orderOrigination }, bytes)

@[simp] theorem encode_length (message : OrderOriginationValue) : (encode message).length = 1 := by
  unfold encode
  simp only [OrderOrigination.encode_length]

theorem encode_length_pos (message : OrderOriginationValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderOriginationValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderOrigination.decode_encode, some_bind]
  rfl

end OrderOriginationValue

/-- Routing Arrangement Indicator: 1 bytes -/
structure RoutingArrangementIndicatorValue where
  routingArrangementIndicator : RoutingArrangementIndicator
  deriving DecidableEq, Repr

namespace RoutingArrangementIndicatorValue

def encode (message : RoutingArrangementIndicatorValue) : List UInt8 :=
  RoutingArrangementIndicator.encode message.routingArrangementIndicator

def decode (bytes : List UInt8) : Option (RoutingArrangementIndicatorValue × List UInt8) := do
  let (routingArrangementIndicator, bytes) ← RoutingArrangementIndicator.decode bytes
  pure ({ routingArrangementIndicator }, bytes)

@[simp] theorem encode_length (message : RoutingArrangementIndicatorValue) : (encode message).length = 1 := by
  unfold encode
  simp only [RoutingArrangementIndicator.encode_length]

theorem encode_length_pos (message : RoutingArrangementIndicatorValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RoutingArrangementIndicatorValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RoutingArrangementIndicator.decode_encode, some_bind]
  rfl

end RoutingArrangementIndicatorValue

/-- Basket Trade: 1 bytes -/
structure BasketTradeValue where
  basketTrade : BasketTrade
  deriving DecidableEq, Repr

namespace BasketTradeValue

def encode (message : BasketTradeValue) : List UInt8 :=
  BasketTrade.encode message.basketTrade

def decode (bytes : List UInt8) : Option (BasketTradeValue × List UInt8) := do
  let (basketTrade, bytes) ← BasketTrade.decode bytes
  pure ({ basketTrade }, bytes)

@[simp] theorem encode_length (message : BasketTradeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [BasketTrade.encode_length]

theorem encode_length_pos (message : BasketTradeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasketTradeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [BasketTrade.decode_encode, some_bind]
  rfl

end BasketTradeValue

/-- Program Trade: 1 bytes -/
structure ProgramTradeValue where
  programTrade : ProgramTrade
  deriving DecidableEq, Repr

namespace ProgramTradeValue

def encode (message : ProgramTradeValue) : List UInt8 :=
  ProgramTrade.encode message.programTrade

def decode (bytes : List UInt8) : Option (ProgramTradeValue × List UInt8) := do
  let (programTrade, bytes) ← ProgramTrade.decode bytes
  pure ({ programTrade }, bytes)

@[simp] theorem encode_length (message : ProgramTradeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [ProgramTrade.encode_length]

theorem encode_length_pos (message : ProgramTradeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProgramTradeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ProgramTrade.decode_encode, some_bind]
  rfl

end ProgramTradeValue

/-- Jitney: 3 bytes -/
structure JitneyValue where
  jitney : Alpha 3
  deriving DecidableEq, Repr

namespace JitneyValue

def encode (message : JitneyValue) : List UInt8 :=
  Alpha.encode message.jitney

def decode (bytes : List UInt8) : Option (JitneyValue × List UInt8) := do
  let (jitney, bytes) ← Alpha.decode 3 bytes
  pure ({ jitney }, bytes)

@[simp] theorem encode_length (message : JitneyValue) : (encode message).length = 3 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : JitneyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : JitneyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end JitneyValue

/-- Gef Eligible: 1 bytes -/
structure GefEligibleValue where
  gefEligible : GefEligible
  deriving DecidableEq, Repr

namespace GefEligibleValue

def encode (message : GefEligibleValue) : List UInt8 :=
  GefEligible.encode message.gefEligible

def decode (bytes : List UInt8) : Option (GefEligibleValue × List UInt8) := do
  let (gefEligible, bytes) ← GefEligible.decode bytes
  pure ({ gefEligible }, bytes)

@[simp] theorem encode_length (message : GefEligibleValue) : (encode message).length = 1 := by
  unfold encode
  simp only [GefEligible.encode_length]

theorem encode_length_pos (message : GefEligibleValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GefEligibleValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [GefEligible.decode_encode, some_bind]
  rfl

end GefEligibleValue

/-- Anonymous: 1 bytes -/
structure AnonymousValue where
  anonymous : Anonymous
  deriving DecidableEq, Repr

namespace AnonymousValue

def encode (message : AnonymousValue) : List UInt8 :=
  Anonymous.encode message.anonymous

def decode (bytes : List UInt8) : Option (AnonymousValue × List UInt8) := do
  let (anonymous, bytes) ← Anonymous.decode bytes
  pure ({ anonymous }, bytes)

@[simp] theorem encode_length (message : AnonymousValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Anonymous.encode_length]

theorem encode_length_pos (message : AnonymousValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AnonymousValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Anonymous.decode_encode, some_bind]
  rfl

end AnonymousValue

/-- Umir Regulation Id: 2 bytes -/
structure UmirRegulationIdValue where
  umirRegulationId : Alpha 2
  deriving DecidableEq, Repr

namespace UmirRegulationIdValue

def encode (message : UmirRegulationIdValue) : List UInt8 :=
  Alpha.encode message.umirRegulationId

def decode (bytes : List UInt8) : Option (UmirRegulationIdValue × List UInt8) := do
  let (umirRegulationId, bytes) ← Alpha.decode 2 bytes
  pure ({ umirRegulationId }, bytes)

@[simp] theorem encode_length (message : UmirRegulationIdValue) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UmirRegulationIdValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UmirRegulationIdValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end UmirRegulationIdValue

/-- Bypass: 1 bytes -/
structure BypassValue where
  bypass : Bypass
  deriving DecidableEq, Repr

namespace BypassValue

def encode (message : BypassValue) : List UInt8 :=
  Bypass.encode message.bypass

def decode (bytes : List UInt8) : Option (BypassValue × List UInt8) := do
  let (bypass, bytes) ← Bypass.decode bytes
  pure ({ bypass }, bytes)

@[simp] theorem encode_length (message : BypassValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Bypass.encode_length]

theorem encode_length_pos (message : BypassValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BypassValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Bypass.decode_encode, some_bind]
  rfl

end BypassValue

/-- Tsxncib: 1 bytes -/
structure TsxncibValue where
  tsxncib : Tsxncib
  deriving DecidableEq, Repr

namespace TsxncibValue

def encode (message : TsxncibValue) : List UInt8 :=
  Tsxncib.encode message.tsxncib

def decode (bytes : List UInt8) : Option (TsxncibValue × List UInt8) := do
  let (tsxncib, bytes) ← Tsxncib.decode bytes
  pure ({ tsxncib }, bytes)

@[simp] theorem encode_length (message : TsxncibValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Tsxncib.encode_length]

theorem encode_length_pos (message : TsxncibValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TsxncibValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Tsxncib.decode_encode, some_bind]
  rfl

end TsxncibValue

/-- No Trade Feat: 1 bytes -/
structure NoTradeFeatValue where
  noTradeFeat : NoTradeFeat
  deriving DecidableEq, Repr

namespace NoTradeFeatValue

def encode (message : NoTradeFeatValue) : List UInt8 :=
  NoTradeFeat.encode message.noTradeFeat

def decode (bytes : List UInt8) : Option (NoTradeFeatValue × List UInt8) := do
  let (noTradeFeat, bytes) ← NoTradeFeat.decode bytes
  pure ({ noTradeFeat }, bytes)

@[simp] theorem encode_length (message : NoTradeFeatValue) : (encode message).length = 1 := by
  unfold encode
  simp only [NoTradeFeat.encode_length]

theorem encode_length_pos (message : NoTradeFeatValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NoTradeFeatValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [NoTradeFeat.decode_encode, some_bind]
  rfl

end NoTradeFeatValue

/-- No Trade Key: 6 bytes -/
structure NoTradeKeyValue where
  noTradeKey : Alpha 6
  deriving DecidableEq, Repr

namespace NoTradeKeyValue

def encode (message : NoTradeKeyValue) : List UInt8 :=
  Alpha.encode message.noTradeKey

def decode (bytes : List UInt8) : Option (NoTradeKeyValue × List UInt8) := do
  let (noTradeKey, bytes) ← Alpha.decode 6 bytes
  pure ({ noTradeKey }, bytes)

@[simp] theorem encode_length (message : NoTradeKeyValue) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : NoTradeKeyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NoTradeKeyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end NoTradeKeyValue

/-- Short Marking Exempt: 1 bytes -/
structure ShortMarkingExemptValue where
  shortMarkingExempt : ShortMarkingExempt
  deriving DecidableEq, Repr

namespace ShortMarkingExemptValue

def encode (message : ShortMarkingExemptValue) : List UInt8 :=
  ShortMarkingExempt.encode message.shortMarkingExempt

def decode (bytes : List UInt8) : Option (ShortMarkingExemptValue × List UInt8) := do
  let (shortMarkingExempt, bytes) ← ShortMarkingExempt.decode bytes
  pure ({ shortMarkingExempt }, bytes)

@[simp] theorem encode_length (message : ShortMarkingExemptValue) : (encode message).length = 1 := by
  unfold encode
  simp only [ShortMarkingExempt.encode_length]

theorem encode_length_pos (message : ShortMarkingExemptValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortMarkingExemptValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ShortMarkingExempt.decode_encode, some_bind]
  rfl

end ShortMarkingExemptValue

/-- Po Comment: 32 bytes -/
structure PoCommentValue where
  poComment : Alpha 32
  deriving DecidableEq, Repr

namespace PoCommentValue

def encode (message : PoCommentValue) : List UInt8 :=
  Alpha.encode message.poComment

def decode (bytes : List UInt8) : Option (PoCommentValue × List UInt8) := do
  let (poComment, bytes) ← Alpha.decode 32 bytes
  pure ({ poComment }, bytes)

@[simp] theorem encode_length (message : PoCommentValue) : (encode message).length = 32 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : PoCommentValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PoCommentValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end PoCommentValue

/-- Display Range: 4 bytes -/
structure DisplayRangeValue where
  displayRange : BitVec 32
  deriving DecidableEq, Repr

namespace DisplayRangeValue

def encode (message : DisplayRangeValue) : List UInt8 :=
  encodeUInt 4 message.displayRange

def decode (bytes : List UInt8) : Option (DisplayRangeValue × List UInt8) := do
  let (displayRange, bytes) ← decodeUInt 4 bytes
  pure ({ displayRange }, bytes)

@[simp] theorem encode_length (message : DisplayRangeValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DisplayRangeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisplayRangeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisplayRangeValue

/-- Customer Account: 20 bytes -/
structure CustomerAccountValue where
  customerAccount : Alpha 20
  deriving DecidableEq, Repr

namespace CustomerAccountValue

def encode (message : CustomerAccountValue) : List UInt8 :=
  Alpha.encode message.customerAccount

def decode (bytes : List UInt8) : Option (CustomerAccountValue × List UInt8) := do
  let (customerAccount, bytes) ← Alpha.decode 20 bytes
  pure ({ customerAccount }, bytes)

@[simp] theorem encode_length (message : CustomerAccountValue) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CustomerAccountValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomerAccountValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CustomerAccountValue

/-- Algorithm Id: 20 bytes -/
structure AlgorithmIdValue where
  algorithmId : Alpha 20
  deriving DecidableEq, Repr

namespace AlgorithmIdValue

def encode (message : AlgorithmIdValue) : List UInt8 :=
  Alpha.encode message.algorithmId

def decode (bytes : List UInt8) : Option (AlgorithmIdValue × List UInt8) := do
  let (algorithmId, bytes) ← Alpha.decode 20 bytes
  pure ({ algorithmId }, bytes)

@[simp] theorem encode_length (message : AlgorithmIdValue) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : AlgorithmIdValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AlgorithmIdValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end AlgorithmIdValue

/-- Customer Lei: 52 bytes -/
structure CustomerLeiValue where
  customerLei : Alpha 52
  deriving DecidableEq, Repr

namespace CustomerLeiValue

def encode (message : CustomerLeiValue) : List UInt8 :=
  Alpha.encode message.customerLei

def decode (bytes : List UInt8) : Option (CustomerLeiValue × List UInt8) := do
  let (customerLei, bytes) ← Alpha.decode 52 bytes
  pure ({ customerLei }, bytes)

@[simp] theorem encode_length (message : CustomerLeiValue) : (encode message).length = 52 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CustomerLeiValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomerLeiValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CustomerLeiValue

/-- Broker Lei: 20 bytes -/
structure BrokerLeiValue where
  brokerLei : Alpha 20
  deriving DecidableEq, Repr

namespace BrokerLeiValue

def encode (message : BrokerLeiValue) : List UInt8 :=
  Alpha.encode message.brokerLei

def decode (bytes : List UInt8) : Option (BrokerLeiValue × List UInt8) := do
  let (brokerLei, bytes) ← Alpha.decode 20 bytes
  pure ({ brokerLei }, bytes)

@[simp] theorem encode_length (message : BrokerLeiValue) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BrokerLeiValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokerLeiValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BrokerLeiValue

/-- Conditional Order: 1 bytes -/
structure ConditionalOrderValue where
  conditionalOrder : ConditionalOrder
  deriving DecidableEq, Repr

namespace ConditionalOrderValue

def encode (message : ConditionalOrderValue) : List UInt8 :=
  ConditionalOrder.encode message.conditionalOrder

def decode (bytes : List UInt8) : Option (ConditionalOrderValue × List UInt8) := do
  let (conditionalOrder_, bytes) ← ConditionalOrder.decode bytes
  pure ({ conditionalOrder := conditionalOrder_ }, bytes)

@[simp] theorem encode_length (message : ConditionalOrderValue) : (encode message).length = 1 := by
  unfold encode
  simp only [ConditionalOrder.encode_length]

theorem encode_length_pos (message : ConditionalOrderValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConditionalOrderValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ConditionalOrder.decode_encode, some_bind]
  rfl

end ConditionalOrderValue

/-- Allow Conditional: 1 bytes -/
structure AllowConditionalValue where
  allowConditional : AllowConditional
  deriving DecidableEq, Repr

namespace AllowConditionalValue

def encode (message : AllowConditionalValue) : List UInt8 :=
  AllowConditional.encode message.allowConditional

def decode (bytes : List UInt8) : Option (AllowConditionalValue × List UInt8) := do
  let (allowConditional, bytes) ← AllowConditional.decode bytes
  pure ({ allowConditional }, bytes)

@[simp] theorem encode_length (message : AllowConditionalValue) : (encode message).length = 1 := by
  unfold encode
  simp only [AllowConditional.encode_length]

theorem encode_length_pos (message : AllowConditionalValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AllowConditionalValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [AllowConditional.decode_encode, some_bind]
  rfl

end AllowConditionalValue

/-- Firm Up Id: 8 bytes -/
structure FirmUpIdValue where
  firmUpId : BitVec 64
  deriving DecidableEq, Repr

namespace FirmUpIdValue

def encode (message : FirmUpIdValue) : List UInt8 :=
  encodeUInt 8 message.firmUpId

def decode (bytes : List UInt8) : Option (FirmUpIdValue × List UInt8) := do
  let (firmUpId, bytes) ← decodeUInt 8 bytes
  pure ({ firmUpId }, bytes)

@[simp] theorem encode_length (message : FirmUpIdValue) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : FirmUpIdValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FirmUpIdValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FirmUpIdValue

/-- Cxd Connect: 1 bytes -/
structure CxdConnectValue where
  cxdConnect : CxdConnect
  deriving DecidableEq, Repr

namespace CxdConnectValue

def encode (message : CxdConnectValue) : List UInt8 :=
  CxdConnect.encode message.cxdConnect

def decode (bytes : List UInt8) : Option (CxdConnectValue × List UInt8) := do
  let (cxdConnect, bytes) ← CxdConnect.decode bytes
  pure ({ cxdConnect }, bytes)

@[simp] theorem encode_length (message : CxdConnectValue) : (encode message).length = 1 := by
  unfold encode
  simp only [CxdConnect.encode_length]

theorem encode_length_pos (message : CxdConnectValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CxdConnectValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [CxdConnect.decode_encode, some_bind]
  rfl

end CxdConnectValue

/-- Pure Stream Connect: 1 bytes -/
structure PureStreamConnectValue where
  pureStreamConnect : PureStreamConnect
  deriving DecidableEq, Repr

namespace PureStreamConnectValue

def encode (message : PureStreamConnectValue) : List UInt8 :=
  PureStreamConnect.encode message.pureStreamConnect

def decode (bytes : List UInt8) : Option (PureStreamConnectValue × List UInt8) := do
  let (pureStreamConnect, bytes) ← PureStreamConnect.decode bytes
  pure ({ pureStreamConnect }, bytes)

@[simp] theorem encode_length (message : PureStreamConnectValue) : (encode message).length = 1 := by
  unfold encode
  simp only [PureStreamConnect.encode_length]

theorem encode_length_pos (message : PureStreamConnectValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PureStreamConnectValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PureStreamConnect.decode_encode, some_bind]
  rfl

end PureStreamConnectValue

/-- Min Rate: 2 bytes -/
structure MinRateValue where
  minRate : BitVec 16
  deriving DecidableEq, Repr

namespace MinRateValue

def encode (message : MinRateValue) : List UInt8 :=
  encodeUInt 2 message.minRate

def decode (bytes : List UInt8) : Option (MinRateValue × List UInt8) := do
  let (minRate, bytes) ← decodeUInt 2 bytes
  pure ({ minRate }, bytes)

@[simp] theorem encode_length (message : MinRateValue) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MinRateValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinRateValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinRateValue

/-- Max Rate: 2 bytes -/
structure MaxRateValue where
  maxRate : BitVec 16
  deriving DecidableEq, Repr

namespace MaxRateValue

def encode (message : MaxRateValue) : List UInt8 :=
  encodeUInt 2 message.maxRate

def decode (bytes : List UInt8) : Option (MaxRateValue × List UInt8) := do
  let (maxRate, bytes) ← decodeUInt 2 bytes
  pure ({ maxRate }, bytes)

@[simp] theorem encode_length (message : MaxRateValue) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MaxRateValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaxRateValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaxRateValue

/-- Routing Strategy: 15 bytes -/
structure RoutingStrategyValue where
  routingStrategy : Alpha 15
  deriving DecidableEq, Repr

namespace RoutingStrategyValue

def encode (message : RoutingStrategyValue) : List UInt8 :=
  Alpha.encode message.routingStrategy

def decode (bytes : List UInt8) : Option (RoutingStrategyValue × List UInt8) := do
  let (routingStrategy, bytes) ← Alpha.decode 15 bytes
  pure ({ routingStrategy }, bytes)

@[simp] theorem encode_length (message : RoutingStrategyValue) : (encode message).length = 15 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : RoutingStrategyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RoutingStrategyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end RoutingStrategyValue

/-- Handl Inst: 1 bytes -/
structure HandlInstValue where
  handlInst : HandlInst
  deriving DecidableEq, Repr

namespace HandlInstValue

def encode (message : HandlInstValue) : List UInt8 :=
  HandlInst.encode message.handlInst

def decode (bytes : List UInt8) : Option (HandlInstValue × List UInt8) := do
  let (handlInst, bytes) ← HandlInst.decode bytes
  pure ({ handlInst }, bytes)

@[simp] theorem encode_length (message : HandlInstValue) : (encode message).length = 1 := by
  unfold encode
  simp only [HandlInst.encode_length]

theorem encode_length_pos (message : HandlInstValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HandlInstValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [HandlInst.decode_encode, some_bind]
  rfl

end HandlInstValue

/-- Reprice Reason: 1 bytes -/
structure RepriceReasonValue where
  repriceReason : BitVec 8
  deriving DecidableEq, Repr

namespace RepriceReasonValue

def encode (message : RepriceReasonValue) : List UInt8 :=
  encodeUInt 1 message.repriceReason

def decode (bytes : List UInt8) : Option (RepriceReasonValue × List UInt8) := do
  let (repriceReason, bytes) ← decodeUInt 1 bytes
  pure ({ repriceReason }, bytes)

@[simp] theorem encode_length (message : RepriceReasonValue) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : RepriceReasonValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RepriceReasonValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RepriceReasonValue

/-- Nbbo Setter: 1 bytes -/
structure NbboSetterValue where
  nbboSetter : NbboSetter
  deriving DecidableEq, Repr

namespace NbboSetterValue

def encode (message : NbboSetterValue) : List UInt8 :=
  NbboSetter.encode message.nbboSetter

def decode (bytes : List UInt8) : Option (NbboSetterValue × List UInt8) := do
  let (nbboSetter_, bytes) ← NbboSetter.decode bytes
  pure ({ nbboSetter := nbboSetter_ }, bytes)

@[simp] theorem encode_length (message : NbboSetterValue) : (encode message).length = 1 := by
  unfold encode
  simp only [NbboSetter.encode_length]

theorem encode_length_pos (message : NbboSetterValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NbboSetterValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [NbboSetter.decode_encode, some_bind]
  rfl

end NbboSetterValue

/-- Any Order Accepted Optional Value, selected by Order Accepted Optional Field -/
inductive OrderAcceptedOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  | account (message : AccountValue) -- 1
  | pegType (message : PegTypeValue) -- 2
  | minQtyType (message : MinQtyTypeValue) -- 3
  | minQty (message : MinQtyValue) -- 4
  | maxFloor (message : MaxFloorValue) -- 5
  | expireTime (message : ExpireTimeValue) -- 6
  | pegOffset (message : PegOffsetValue) -- 7
  | targetStrategy (message : TargetStrategyValue) -- 8
  | orderOrigination (message : OrderOriginationValue) -- 9
  | routingArrangementIndicator (message : RoutingArrangementIndicatorValue) -- 10
  | basketTrade (message : BasketTradeValue) -- 11
  | programTrade (message : ProgramTradeValue) -- 12
  | jitney (message : JitneyValue) -- 14
  | gefEligible (message : GefEligibleValue) -- 15
  | anonymous (message : AnonymousValue) -- 16
  | umirRegulationId (message : UmirRegulationIdValue) -- 17
  | bypass (message : BypassValue) -- 18
  | tsxncib (message : TsxncibValue) -- 19
  | noTradeFeat (message : NoTradeFeatValue) -- 20
  | noTradeKey (message : NoTradeKeyValue) -- 21
  | shortMarkingExempt (message : ShortMarkingExemptValue) -- 22
  | poComment (message : PoCommentValue) -- 23
  | displayRange (message : DisplayRangeValue) -- 24
  | customerAccount (message : CustomerAccountValue) -- 25
  | algorithmId (message : AlgorithmIdValue) -- 26
  | customerLei (message : CustomerLeiValue) -- 27
  | brokerLei (message : BrokerLeiValue) -- 28
  | conditionalOrder (message : ConditionalOrderValue) -- 29
  | allowConditional (message : AllowConditionalValue) -- 30
  | firmUpId (message : FirmUpIdValue) -- 31
  | cxdConnect (message : CxdConnectValue) -- 32
  | pureStreamConnect (message : PureStreamConnectValue) -- 33
  | minRate (message : MinRateValue) -- 34
  | maxRate (message : MaxRateValue) -- 35
  | routingStrategy (message : RoutingStrategyValue) -- 39
  | handlInst (message : HandlInstValue) -- 43
  | repriceReason (message : RepriceReasonValue) -- 44
  | nbboSetter (message : NbboSetterValue) -- 45
  deriving DecidableEq, Repr

namespace OrderAcceptedOptionalValue

/-- The Order Accepted Optional Field each message is sent under -/
def tag : OrderAcceptedOptionalValue → BitVec 8
  | .userRefIdx _ => 37
  | .account _ => 1
  | .pegType _ => 2
  | .minQtyType _ => 3
  | .minQty _ => 4
  | .maxFloor _ => 5
  | .expireTime _ => 6
  | .pegOffset _ => 7
  | .targetStrategy _ => 8
  | .orderOrigination _ => 9
  | .routingArrangementIndicator _ => 10
  | .basketTrade _ => 11
  | .programTrade _ => 12
  | .jitney _ => 14
  | .gefEligible _ => 15
  | .anonymous _ => 16
  | .umirRegulationId _ => 17
  | .bypass _ => 18
  | .tsxncib _ => 19
  | .noTradeFeat _ => 20
  | .noTradeKey _ => 21
  | .shortMarkingExempt _ => 22
  | .poComment _ => 23
  | .displayRange _ => 24
  | .customerAccount _ => 25
  | .algorithmId _ => 26
  | .customerLei _ => 27
  | .brokerLei _ => 28
  | .conditionalOrder _ => 29
  | .allowConditional _ => 30
  | .firmUpId _ => 31
  | .cxdConnect _ => 32
  | .pureStreamConnect _ => 33
  | .minRate _ => 34
  | .maxRate _ => 35
  | .routingStrategy _ => 39
  | .handlInst _ => 43
  | .repriceReason _ => 44
  | .nbboSetter _ => 45

def encode : OrderAcceptedOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message
  | .account message => AccountValue.encode message
  | .pegType message => PegTypeValue.encode message
  | .minQtyType message => MinQtyTypeValue.encode message
  | .minQty message => MinQtyValue.encode message
  | .maxFloor message => MaxFloorValue.encode message
  | .expireTime message => ExpireTimeValue.encode message
  | .pegOffset message => PegOffsetValue.encode message
  | .targetStrategy message => TargetStrategyValue.encode message
  | .orderOrigination message => OrderOriginationValue.encode message
  | .routingArrangementIndicator message => RoutingArrangementIndicatorValue.encode message
  | .basketTrade message => BasketTradeValue.encode message
  | .programTrade message => ProgramTradeValue.encode message
  | .jitney message => JitneyValue.encode message
  | .gefEligible message => GefEligibleValue.encode message
  | .anonymous message => AnonymousValue.encode message
  | .umirRegulationId message => UmirRegulationIdValue.encode message
  | .bypass message => BypassValue.encode message
  | .tsxncib message => TsxncibValue.encode message
  | .noTradeFeat message => NoTradeFeatValue.encode message
  | .noTradeKey message => NoTradeKeyValue.encode message
  | .shortMarkingExempt message => ShortMarkingExemptValue.encode message
  | .poComment message => PoCommentValue.encode message
  | .displayRange message => DisplayRangeValue.encode message
  | .customerAccount message => CustomerAccountValue.encode message
  | .algorithmId message => AlgorithmIdValue.encode message
  | .customerLei message => CustomerLeiValue.encode message
  | .brokerLei message => BrokerLeiValue.encode message
  | .conditionalOrder message => ConditionalOrderValue.encode message
  | .allowConditional message => AllowConditionalValue.encode message
  | .firmUpId message => FirmUpIdValue.encode message
  | .cxdConnect message => CxdConnectValue.encode message
  | .pureStreamConnect message => PureStreamConnectValue.encode message
  | .minRate message => MinRateValue.encode message
  | .maxRate message => MaxRateValue.encode message
  | .routingStrategy message => RoutingStrategyValue.encode message
  | .handlInst message => HandlInstValue.encode message
  | .repriceReason message => RepriceReasonValue.encode message
  | .nbboSetter message => NbboSetterValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderAcceptedOptionalValue) : (encode message).length ≤ 52 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega
  | account inner =>
    simp only [encode, AccountValue.encode_length]
    omega
  | pegType inner =>
    simp only [encode, PegTypeValue.encode_length]
    omega
  | minQtyType inner =>
    simp only [encode, MinQtyTypeValue.encode_length]
    omega
  | minQty inner =>
    simp only [encode, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [encode, MaxFloorValue.encode_length]
    omega
  | expireTime inner =>
    simp only [encode, ExpireTimeValue.encode_length]
    omega
  | pegOffset inner =>
    simp only [encode, PegOffsetValue.encode_length]
    omega
  | targetStrategy inner =>
    simp only [encode, TargetStrategyValue.encode_length]
    omega
  | orderOrigination inner =>
    simp only [encode, OrderOriginationValue.encode_length]
    omega
  | routingArrangementIndicator inner =>
    simp only [encode, RoutingArrangementIndicatorValue.encode_length]
    omega
  | basketTrade inner =>
    simp only [encode, BasketTradeValue.encode_length]
    omega
  | programTrade inner =>
    simp only [encode, ProgramTradeValue.encode_length]
    omega
  | jitney inner =>
    simp only [encode, JitneyValue.encode_length]
    omega
  | gefEligible inner =>
    simp only [encode, GefEligibleValue.encode_length]
    omega
  | anonymous inner =>
    simp only [encode, AnonymousValue.encode_length]
    omega
  | umirRegulationId inner =>
    simp only [encode, UmirRegulationIdValue.encode_length]
    omega
  | bypass inner =>
    simp only [encode, BypassValue.encode_length]
    omega
  | tsxncib inner =>
    simp only [encode, TsxncibValue.encode_length]
    omega
  | noTradeFeat inner =>
    simp only [encode, NoTradeFeatValue.encode_length]
    omega
  | noTradeKey inner =>
    simp only [encode, NoTradeKeyValue.encode_length]
    omega
  | shortMarkingExempt inner =>
    simp only [encode, ShortMarkingExemptValue.encode_length]
    omega
  | poComment inner =>
    simp only [encode, PoCommentValue.encode_length]
    omega
  | displayRange inner =>
    simp only [encode, DisplayRangeValue.encode_length]
    omega
  | customerAccount inner =>
    simp only [encode, CustomerAccountValue.encode_length]
    omega
  | algorithmId inner =>
    simp only [encode, AlgorithmIdValue.encode_length]
    omega
  | customerLei inner =>
    simp only [encode, CustomerLeiValue.encode_length]
    omega
  | brokerLei inner =>
    simp only [encode, BrokerLeiValue.encode_length]
    omega
  | conditionalOrder inner =>
    simp only [encode, ConditionalOrderValue.encode_length]
    omega
  | allowConditional inner =>
    simp only [encode, AllowConditionalValue.encode_length]
    omega
  | firmUpId inner =>
    simp only [encode, FirmUpIdValue.encode_length]
    omega
  | cxdConnect inner =>
    simp only [encode, CxdConnectValue.encode_length]
    omega
  | pureStreamConnect inner =>
    simp only [encode, PureStreamConnectValue.encode_length]
    omega
  | minRate inner =>
    simp only [encode, MinRateValue.encode_length]
    omega
  | maxRate inner =>
    simp only [encode, MaxRateValue.encode_length]
    omega
  | routingStrategy inner =>
    simp only [encode, RoutingStrategyValue.encode_length]
    omega
  | handlInst inner =>
    simp only [encode, HandlInstValue.encode_length]
    omega
  | repriceReason inner =>
    simp only [encode, RepriceReasonValue.encode_length]
    omega
  | nbboSetter inner =>
    simp only [encode, NbboSetterValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderAcceptedOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else if tag = 1 then (AccountValue.decode bytes).map fun (message, rest) => (.account message, rest)
  else if tag = 2 then (PegTypeValue.decode bytes).map fun (message, rest) => (.pegType message, rest)
  else if tag = 3 then (MinQtyTypeValue.decode bytes).map fun (message, rest) => (.minQtyType message, rest)
  else if tag = 4 then (MinQtyValue.decode bytes).map fun (message, rest) => (.minQty message, rest)
  else if tag = 5 then (MaxFloorValue.decode bytes).map fun (message, rest) => (.maxFloor message, rest)
  else if tag = 6 then (ExpireTimeValue.decode bytes).map fun (message, rest) => (.expireTime message, rest)
  else if tag = 7 then (PegOffsetValue.decode bytes).map fun (message, rest) => (.pegOffset message, rest)
  else if tag = 8 then (TargetStrategyValue.decode bytes).map fun (message, rest) => (.targetStrategy message, rest)
  else if tag = 9 then (OrderOriginationValue.decode bytes).map fun (message, rest) => (.orderOrigination message, rest)
  else if tag = 10 then (RoutingArrangementIndicatorValue.decode bytes).map fun (message, rest) => (.routingArrangementIndicator message, rest)
  else if tag = 11 then (BasketTradeValue.decode bytes).map fun (message, rest) => (.basketTrade message, rest)
  else if tag = 12 then (ProgramTradeValue.decode bytes).map fun (message, rest) => (.programTrade message, rest)
  else if tag = 14 then (JitneyValue.decode bytes).map fun (message, rest) => (.jitney message, rest)
  else if tag = 15 then (GefEligibleValue.decode bytes).map fun (message, rest) => (.gefEligible message, rest)
  else if tag = 16 then (AnonymousValue.decode bytes).map fun (message, rest) => (.anonymous message, rest)
  else if tag = 17 then (UmirRegulationIdValue.decode bytes).map fun (message, rest) => (.umirRegulationId message, rest)
  else if tag = 18 then (BypassValue.decode bytes).map fun (message, rest) => (.bypass message, rest)
  else if tag = 19 then (TsxncibValue.decode bytes).map fun (message, rest) => (.tsxncib message, rest)
  else if tag = 20 then (NoTradeFeatValue.decode bytes).map fun (message, rest) => (.noTradeFeat message, rest)
  else if tag = 21 then (NoTradeKeyValue.decode bytes).map fun (message, rest) => (.noTradeKey message, rest)
  else if tag = 22 then (ShortMarkingExemptValue.decode bytes).map fun (message, rest) => (.shortMarkingExempt message, rest)
  else if tag = 23 then (PoCommentValue.decode bytes).map fun (message, rest) => (.poComment message, rest)
  else if tag = 24 then (DisplayRangeValue.decode bytes).map fun (message, rest) => (.displayRange message, rest)
  else if tag = 25 then (CustomerAccountValue.decode bytes).map fun (message, rest) => (.customerAccount message, rest)
  else if tag = 26 then (AlgorithmIdValue.decode bytes).map fun (message, rest) => (.algorithmId message, rest)
  else if tag = 27 then (CustomerLeiValue.decode bytes).map fun (message, rest) => (.customerLei message, rest)
  else if tag = 28 then (BrokerLeiValue.decode bytes).map fun (message, rest) => (.brokerLei message, rest)
  else if tag = 29 then (ConditionalOrderValue.decode bytes).map fun (message, rest) => (.conditionalOrder message, rest)
  else if tag = 30 then (AllowConditionalValue.decode bytes).map fun (message, rest) => (.allowConditional message, rest)
  else if tag = 31 then (FirmUpIdValue.decode bytes).map fun (message, rest) => (.firmUpId message, rest)
  else if tag = 32 then (CxdConnectValue.decode bytes).map fun (message, rest) => (.cxdConnect message, rest)
  else if tag = 33 then (PureStreamConnectValue.decode bytes).map fun (message, rest) => (.pureStreamConnect message, rest)
  else if tag = 34 then (MinRateValue.decode bytes).map fun (message, rest) => (.minRate message, rest)
  else if tag = 35 then (MaxRateValue.decode bytes).map fun (message, rest) => (.maxRate message, rest)
  else if tag = 39 then (RoutingStrategyValue.decode bytes).map fun (message, rest) => (.routingStrategy message, rest)
  else if tag = 43 then (HandlInstValue.decode bytes).map fun (message, rest) => (.handlInst message, rest)
  else if tag = 44 then (RepriceReasonValue.decode bytes).map fun (message, rest) => (.repriceReason message, rest)
  else if tag = 45 then (NbboSetterValue.decode bytes).map fun (message, rest) => (.nbboSetter message, rest)
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
  | userRefIdx inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega
  | account inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, AccountValue.encode_length]
    omega
  | pegType inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, PegTypeValue.encode_length]
    omega
  | minQtyType inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyTypeValue.encode_length]
    omega
  | minQty inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, MaxFloorValue.encode_length]
    omega
  | expireTime inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, ExpireTimeValue.encode_length]
    omega
  | pegOffset inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, PegOffsetValue.encode_length]
    omega
  | targetStrategy inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, TargetStrategyValue.encode_length]
    omega
  | orderOrigination inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, OrderOriginationValue.encode_length]
    omega
  | routingArrangementIndicator inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, RoutingArrangementIndicatorValue.encode_length]
    omega
  | basketTrade inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, BasketTradeValue.encode_length]
    omega
  | programTrade inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, ProgramTradeValue.encode_length]
    omega
  | jitney inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, JitneyValue.encode_length]
    omega
  | gefEligible inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, GefEligibleValue.encode_length]
    omega
  | anonymous inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, AnonymousValue.encode_length]
    omega
  | umirRegulationId inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, UmirRegulationIdValue.encode_length]
    omega
  | bypass inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, BypassValue.encode_length]
    omega
  | tsxncib inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, TsxncibValue.encode_length]
    omega
  | noTradeFeat inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, NoTradeFeatValue.encode_length]
    omega
  | noTradeKey inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, NoTradeKeyValue.encode_length]
    omega
  | shortMarkingExempt inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, ShortMarkingExemptValue.encode_length]
    omega
  | poComment inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, PoCommentValue.encode_length]
    omega
  | displayRange inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, DisplayRangeValue.encode_length]
    omega
  | customerAccount inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, CustomerAccountValue.encode_length]
    omega
  | algorithmId inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, AlgorithmIdValue.encode_length]
    omega
  | customerLei inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, CustomerLeiValue.encode_length]
    omega
  | brokerLei inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, BrokerLeiValue.encode_length]
    omega
  | conditionalOrder inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, ConditionalOrderValue.encode_length]
    omega
  | allowConditional inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, AllowConditionalValue.encode_length]
    omega
  | firmUpId inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, FirmUpIdValue.encode_length]
    omega
  | cxdConnect inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, CxdConnectValue.encode_length]
    omega
  | pureStreamConnect inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, PureStreamConnectValue.encode_length]
    omega
  | minRate inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, MinRateValue.encode_length]
    omega
  | maxRate inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, MaxRateValue.encode_length]
    omega
  | routingStrategy inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, RoutingStrategyValue.encode_length]
    omega
  | handlInst inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, HandlInstValue.encode_length]
    omega
  | repriceReason inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, RepriceReasonValue.encode_length]
    omega
  | nbboSetter inner =>
    simp only [OrderAcceptedOptionalValue.encode, List.length_append, encodeUInt_length, NbboSetterValue.encode_length]
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
  orderQty : BitVec 32
  price : BitVec 64
  side : Side
  symbol : Alpha 10
  timeInForce : TimeInForce
  exDestination : ExDestination
  umirAccountType : Alpha 2
  umirUserId : Alpha 8
  orderReferenceNumber : BitVec 64
  orderState : OrderState
  orderAcceptedAppendage : Sized 2 OrderAcceptedAppendage.encode
  deriving DecidableEq, Repr

namespace OrderAcceptedMessage

def encode (message : OrderAcceptedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Side.encode message.side
    ++ (Alpha.encode message.symbol
    ++ (TimeInForce.encode message.timeInForce
    ++ (ExDestination.encode message.exDestination
    ++ (Alpha.encode message.umirAccountType
    ++ (Alpha.encode message.umirUserId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (OrderState.encode message.orderState
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderAcceptedAppendage.encode message.orderAcceptedAppendage.val).length)
    ++ (encodeMany OrderAcceptedAppendage.encode message.orderAcceptedAppendage.val)))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcceptedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (exDestination, bytes) ← ExDestination.decode bytes
  let (umirAccountType, bytes) ← Alpha.decode 2 bytes
  let (umirUserId, bytes) ← Alpha.decode 8 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (orderAcceptedAppendage_, bytes) ← decodeSized OrderAcceptedAppendage.decode appendageLength.toNat bytes
  if fits_orderAcceptedAppendage : (encodeMany OrderAcceptedAppendage.encode orderAcceptedAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, orderQty, price, side, symbol, timeInForce, exDestination, umirAccountType, umirUserId, orderReferenceNumber, orderState, orderAcceptedAppendage := ⟨orderAcceptedAppendage_, fits_orderAcceptedAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderAcceptedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderAcceptedMessage) : (encode message).length ≤ 65593 := by
  have bound_orderAcceptedAppendage := message.orderAcceptedAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Side.encode_length, Alpha.encode_length, TimeInForce.encode_length, ExDestination.encode_length, OrderState.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderAcceptedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExDestination.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
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

/-- Any Order Replaced Optional Value, selected by Order Replaced Optional Field -/
inductive OrderReplacedOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  | minQtyType (message : MinQtyTypeValue) -- 3
  | pegType (message : PegTypeValue) -- 2
  | minQty (message : MinQtyValue) -- 4
  | maxFloor (message : MaxFloorValue) -- 5
  | expireTime (message : ExpireTimeValue) -- 6
  | pegOffset (message : PegOffsetValue) -- 7
  | targetStrategy (message : TargetStrategyValue) -- 8
  | orderOrigination (message : OrderOriginationValue) -- 9
  | routingArrangementIndicator (message : RoutingArrangementIndicatorValue) -- 10
  | umirRegulationId (message : UmirRegulationIdValue) -- 17
  | anonymous (message : AnonymousValue) -- 16
  | displayRange (message : DisplayRangeValue) -- 24
  | customerAccount (message : CustomerAccountValue) -- 25
  | algorithmId (message : AlgorithmIdValue) -- 26
  | customerLei (message : CustomerLeiValue) -- 27
  | brokerLei (message : BrokerLeiValue) -- 28
  | allowConditional (message : AllowConditionalValue) -- 30
  | cxdConnect (message : CxdConnectValue) -- 32
  | pureStreamConnect (message : PureStreamConnectValue) -- 33
  | minRate (message : MinRateValue) -- 34
  | maxRate (message : MaxRateValue) -- 35
  | handlInst (message : HandlInstValue) -- 43
  | repriceReason (message : RepriceReasonValue) -- 44
  | nbboSetter (message : NbboSetterValue) -- 45
  deriving DecidableEq, Repr

namespace OrderReplacedOptionalValue

/-- The Order Replaced Optional Field each message is sent under -/
def tag : OrderReplacedOptionalValue → BitVec 8
  | .userRefIdx _ => 37
  | .minQtyType _ => 3
  | .pegType _ => 2
  | .minQty _ => 4
  | .maxFloor _ => 5
  | .expireTime _ => 6
  | .pegOffset _ => 7
  | .targetStrategy _ => 8
  | .orderOrigination _ => 9
  | .routingArrangementIndicator _ => 10
  | .umirRegulationId _ => 17
  | .anonymous _ => 16
  | .displayRange _ => 24
  | .customerAccount _ => 25
  | .algorithmId _ => 26
  | .customerLei _ => 27
  | .brokerLei _ => 28
  | .allowConditional _ => 30
  | .cxdConnect _ => 32
  | .pureStreamConnect _ => 33
  | .minRate _ => 34
  | .maxRate _ => 35
  | .handlInst _ => 43
  | .repriceReason _ => 44
  | .nbboSetter _ => 45

def encode : OrderReplacedOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message
  | .minQtyType message => MinQtyTypeValue.encode message
  | .pegType message => PegTypeValue.encode message
  | .minQty message => MinQtyValue.encode message
  | .maxFloor message => MaxFloorValue.encode message
  | .expireTime message => ExpireTimeValue.encode message
  | .pegOffset message => PegOffsetValue.encode message
  | .targetStrategy message => TargetStrategyValue.encode message
  | .orderOrigination message => OrderOriginationValue.encode message
  | .routingArrangementIndicator message => RoutingArrangementIndicatorValue.encode message
  | .umirRegulationId message => UmirRegulationIdValue.encode message
  | .anonymous message => AnonymousValue.encode message
  | .displayRange message => DisplayRangeValue.encode message
  | .customerAccount message => CustomerAccountValue.encode message
  | .algorithmId message => AlgorithmIdValue.encode message
  | .customerLei message => CustomerLeiValue.encode message
  | .brokerLei message => BrokerLeiValue.encode message
  | .allowConditional message => AllowConditionalValue.encode message
  | .cxdConnect message => CxdConnectValue.encode message
  | .pureStreamConnect message => PureStreamConnectValue.encode message
  | .minRate message => MinRateValue.encode message
  | .maxRate message => MaxRateValue.encode message
  | .handlInst message => HandlInstValue.encode message
  | .repriceReason message => RepriceReasonValue.encode message
  | .nbboSetter message => NbboSetterValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderReplacedOptionalValue) : (encode message).length ≤ 52 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega
  | minQtyType inner =>
    simp only [encode, MinQtyTypeValue.encode_length]
    omega
  | pegType inner =>
    simp only [encode, PegTypeValue.encode_length]
    omega
  | minQty inner =>
    simp only [encode, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [encode, MaxFloorValue.encode_length]
    omega
  | expireTime inner =>
    simp only [encode, ExpireTimeValue.encode_length]
    omega
  | pegOffset inner =>
    simp only [encode, PegOffsetValue.encode_length]
    omega
  | targetStrategy inner =>
    simp only [encode, TargetStrategyValue.encode_length]
    omega
  | orderOrigination inner =>
    simp only [encode, OrderOriginationValue.encode_length]
    omega
  | routingArrangementIndicator inner =>
    simp only [encode, RoutingArrangementIndicatorValue.encode_length]
    omega
  | umirRegulationId inner =>
    simp only [encode, UmirRegulationIdValue.encode_length]
    omega
  | anonymous inner =>
    simp only [encode, AnonymousValue.encode_length]
    omega
  | displayRange inner =>
    simp only [encode, DisplayRangeValue.encode_length]
    omega
  | customerAccount inner =>
    simp only [encode, CustomerAccountValue.encode_length]
    omega
  | algorithmId inner =>
    simp only [encode, AlgorithmIdValue.encode_length]
    omega
  | customerLei inner =>
    simp only [encode, CustomerLeiValue.encode_length]
    omega
  | brokerLei inner =>
    simp only [encode, BrokerLeiValue.encode_length]
    omega
  | allowConditional inner =>
    simp only [encode, AllowConditionalValue.encode_length]
    omega
  | cxdConnect inner =>
    simp only [encode, CxdConnectValue.encode_length]
    omega
  | pureStreamConnect inner =>
    simp only [encode, PureStreamConnectValue.encode_length]
    omega
  | minRate inner =>
    simp only [encode, MinRateValue.encode_length]
    omega
  | maxRate inner =>
    simp only [encode, MaxRateValue.encode_length]
    omega
  | handlInst inner =>
    simp only [encode, HandlInstValue.encode_length]
    omega
  | repriceReason inner =>
    simp only [encode, RepriceReasonValue.encode_length]
    omega
  | nbboSetter inner =>
    simp only [encode, NbboSetterValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderReplacedOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else if tag = 3 then (MinQtyTypeValue.decode bytes).map fun (message, rest) => (.minQtyType message, rest)
  else if tag = 2 then (PegTypeValue.decode bytes).map fun (message, rest) => (.pegType message, rest)
  else if tag = 4 then (MinQtyValue.decode bytes).map fun (message, rest) => (.minQty message, rest)
  else if tag = 5 then (MaxFloorValue.decode bytes).map fun (message, rest) => (.maxFloor message, rest)
  else if tag = 6 then (ExpireTimeValue.decode bytes).map fun (message, rest) => (.expireTime message, rest)
  else if tag = 7 then (PegOffsetValue.decode bytes).map fun (message, rest) => (.pegOffset message, rest)
  else if tag = 8 then (TargetStrategyValue.decode bytes).map fun (message, rest) => (.targetStrategy message, rest)
  else if tag = 9 then (OrderOriginationValue.decode bytes).map fun (message, rest) => (.orderOrigination message, rest)
  else if tag = 10 then (RoutingArrangementIndicatorValue.decode bytes).map fun (message, rest) => (.routingArrangementIndicator message, rest)
  else if tag = 17 then (UmirRegulationIdValue.decode bytes).map fun (message, rest) => (.umirRegulationId message, rest)
  else if tag = 16 then (AnonymousValue.decode bytes).map fun (message, rest) => (.anonymous message, rest)
  else if tag = 24 then (DisplayRangeValue.decode bytes).map fun (message, rest) => (.displayRange message, rest)
  else if tag = 25 then (CustomerAccountValue.decode bytes).map fun (message, rest) => (.customerAccount message, rest)
  else if tag = 26 then (AlgorithmIdValue.decode bytes).map fun (message, rest) => (.algorithmId message, rest)
  else if tag = 27 then (CustomerLeiValue.decode bytes).map fun (message, rest) => (.customerLei message, rest)
  else if tag = 28 then (BrokerLeiValue.decode bytes).map fun (message, rest) => (.brokerLei message, rest)
  else if tag = 30 then (AllowConditionalValue.decode bytes).map fun (message, rest) => (.allowConditional message, rest)
  else if tag = 32 then (CxdConnectValue.decode bytes).map fun (message, rest) => (.cxdConnect message, rest)
  else if tag = 33 then (PureStreamConnectValue.decode bytes).map fun (message, rest) => (.pureStreamConnect message, rest)
  else if tag = 34 then (MinRateValue.decode bytes).map fun (message, rest) => (.minRate message, rest)
  else if tag = 35 then (MaxRateValue.decode bytes).map fun (message, rest) => (.maxRate message, rest)
  else if tag = 43 then (HandlInstValue.decode bytes).map fun (message, rest) => (.handlInst message, rest)
  else if tag = 44 then (RepriceReasonValue.decode bytes).map fun (message, rest) => (.repriceReason message, rest)
  else if tag = 45 then (NbboSetterValue.decode bytes).map fun (message, rest) => (.nbboSetter message, rest)
  else none

@[simp] theorem decode_encode (message : OrderReplacedOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end OrderReplacedOptionalValue

/-- Order Replaced Appendage -/
structure OrderReplacedAppendage where
  orderReplacedOptionalValue : OrderReplacedOptionalValue
  deriving DecidableEq, Repr

namespace OrderReplacedAppendage

def encodeBody (message : OrderReplacedAppendage) : List UInt8 :=
  encodeUInt 1 (OrderReplacedOptionalValue.tag message.orderReplacedOptionalValue)
    ++ (OrderReplacedOptionalValue.encode message.orderReplacedOptionalValue)

def decodeBody (bytes : List UInt8) : Option (OrderReplacedAppendage × List UInt8) := do
  let (orderReplacedOptionalField, bytes) ← decodeUInt 1 bytes
  let (orderReplacedOptionalValue, bytes) ← OrderReplacedOptionalValue.decode orderReplacedOptionalField bytes
  pure ({ orderReplacedOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : OrderReplacedAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderReplacedOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OrderReplacedAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.orderReplacedOptionalValue with
  | userRefIdx inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega
  | minQtyType inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyTypeValue.encode_length]
    omega
  | pegType inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, PegTypeValue.encode_length]
    omega
  | minQty inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, MaxFloorValue.encode_length]
    omega
  | expireTime inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, ExpireTimeValue.encode_length]
    omega
  | pegOffset inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, PegOffsetValue.encode_length]
    omega
  | targetStrategy inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, TargetStrategyValue.encode_length]
    omega
  | orderOrigination inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, OrderOriginationValue.encode_length]
    omega
  | routingArrangementIndicator inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, RoutingArrangementIndicatorValue.encode_length]
    omega
  | umirRegulationId inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, UmirRegulationIdValue.encode_length]
    omega
  | anonymous inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, AnonymousValue.encode_length]
    omega
  | displayRange inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, DisplayRangeValue.encode_length]
    omega
  | customerAccount inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, CustomerAccountValue.encode_length]
    omega
  | algorithmId inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, AlgorithmIdValue.encode_length]
    omega
  | customerLei inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, CustomerLeiValue.encode_length]
    omega
  | brokerLei inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, BrokerLeiValue.encode_length]
    omega
  | allowConditional inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, AllowConditionalValue.encode_length]
    omega
  | cxdConnect inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, CxdConnectValue.encode_length]
    omega
  | pureStreamConnect inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, PureStreamConnectValue.encode_length]
    omega
  | minRate inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, MinRateValue.encode_length]
    omega
  | maxRate inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, MaxRateValue.encode_length]
    omega
  | handlInst inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, HandlInstValue.encode_length]
    omega
  | repriceReason inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, RepriceReasonValue.encode_length]
    omega
  | nbboSetter inner =>
    simp only [OrderReplacedOptionalValue.encode, List.length_append, encodeUInt_length, NbboSetterValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : OrderReplacedAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (OrderReplacedAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : OrderReplacedAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OrderReplacedAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end OrderReplacedAppendage

/-- Order Replaced Message -/
structure OrderReplacedMessage where
  timestamp : BitVec 64
  origUserRefNum : BitVec 32
  userRefNum : BitVec 32
  orderQty : BitVec 32
  price : BitVec 64
  side : Side
  timeInForce : TimeInForce
  orderReferenceNumber : BitVec 64
  orderState : OrderState
  orderReplacedAppendage : Sized 2 OrderReplacedAppendage.encode
  deriving DecidableEq, Repr

namespace OrderReplacedMessage

def encode (message : OrderReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.origUserRefNum
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Side.encode message.side
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (OrderState.encode message.orderState
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderReplacedAppendage.encode message.orderReplacedAppendage.val).length)
    ++ (encodeMany OrderReplacedAppendage.encode message.orderReplacedAppendage.val))))))))))

def decode (bytes : List UInt8) : Option (OrderReplacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (origUserRefNum, bytes) ← decodeUInt 4 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (orderState, bytes) ← OrderState.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (orderReplacedAppendage_, bytes) ← decodeSized OrderReplacedAppendage.decode appendageLength.toNat bytes
  if fits_orderReplacedAppendage : (encodeMany OrderReplacedAppendage.encode orderReplacedAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, origUserRefNum, userRefNum, orderQty, price, side, timeInForce, orderReferenceNumber, orderState, orderReplacedAppendage := ⟨orderReplacedAppendage_, fits_orderReplacedAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderReplacedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderReplacedMessage) : (encode message).length ≤ 65576 := by
  have bound_orderReplacedAppendage := message.orderReplacedAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Side.encode_length, TimeInForce.encode_length, OrderState.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderReplacedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 OrderReplacedAppendage.encode OrderReplacedAppendage.decode OrderReplacedAppendage.decode_encode OrderReplacedAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.orderReplacedAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderReplacedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderReplacedMessage

/-- Any Order Canceled Optional Value, selected by Order Canceled Optional Field -/
inductive OrderCanceledOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  deriving DecidableEq, Repr

namespace OrderCanceledOptionalValue

/-- The Order Canceled Optional Field each message is sent under -/
def tag : OrderCanceledOptionalValue → BitVec 8
  | .userRefIdx _ => 37

def encode : OrderCanceledOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderCanceledOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderCanceledOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : OrderCanceledOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end OrderCanceledOptionalValue

/-- Order Canceled Appendage -/
structure OrderCanceledAppendage where
  orderCanceledOptionalValue : OrderCanceledOptionalValue
  deriving DecidableEq, Repr

namespace OrderCanceledAppendage

def encodeBody (message : OrderCanceledAppendage) : List UInt8 :=
  encodeUInt 1 (OrderCanceledOptionalValue.tag message.orderCanceledOptionalValue)
    ++ (OrderCanceledOptionalValue.encode message.orderCanceledOptionalValue)

def decodeBody (bytes : List UInt8) : Option (OrderCanceledAppendage × List UInt8) := do
  let (orderCanceledOptionalField, bytes) ← decodeUInt 1 bytes
  let (orderCanceledOptionalValue, bytes) ← OrderCanceledOptionalValue.decode orderCanceledOptionalField bytes
  pure ({ orderCanceledOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : OrderCanceledAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderCanceledOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OrderCanceledAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.orderCanceledOptionalValue with
  | userRefIdx inner =>
    simp only [OrderCanceledOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : OrderCanceledAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (OrderCanceledAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : OrderCanceledAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OrderCanceledAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end OrderCanceledAppendage

/-- Order Canceled Message -/
structure OrderCanceledMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  orderQty : BitVec 32
  cancelReason : Alpha 4
  orderCanceledAppendage : Sized 2 OrderCanceledAppendage.encode
  deriving DecidableEq, Repr

namespace OrderCanceledMessage

def encode (message : OrderCanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.orderQty
    ++ (Alpha.encode message.cancelReason
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderCanceledAppendage.encode message.orderCanceledAppendage.val).length)
    ++ (encodeMany OrderCanceledAppendage.encode message.orderCanceledAppendage.val)))))

def decode (bytes : List UInt8) : Option (OrderCanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (cancelReason, bytes) ← Alpha.decode 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (orderCanceledAppendage_, bytes) ← decodeSized OrderCanceledAppendage.decode appendageLength.toNat bytes
  if fits_orderCanceledAppendage : (encodeMany OrderCanceledAppendage.encode orderCanceledAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, orderQty, cancelReason, orderCanceledAppendage := ⟨orderCanceledAppendage_, fits_orderCanceledAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderCanceledMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderCanceledMessage) : (encode message).length ≤ 65557 := by
  have bound_orderCanceledAppendage := message.orderCanceledAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 OrderCanceledAppendage.encode OrderCanceledAppendage.decode OrderCanceledAppendage.decode_encode OrderCanceledAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.orderCanceledAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderCanceledMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderCanceledMessage

/-- Any Stp Canceled Optional Value, selected by Stp Canceled Optional Field -/
inductive StpCanceledOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  deriving DecidableEq, Repr

namespace StpCanceledOptionalValue

/-- The Stp Canceled Optional Field each message is sent under -/
def tag : StpCanceledOptionalValue → BitVec 8
  | .userRefIdx _ => 37

def encode : StpCanceledOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : StpCanceledOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (StpCanceledOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : StpCanceledOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end StpCanceledOptionalValue

/-- Stp Canceled Appendage -/
structure StpCanceledAppendage where
  stpCanceledOptionalValue : StpCanceledOptionalValue
  deriving DecidableEq, Repr

namespace StpCanceledAppendage

def encodeBody (message : StpCanceledAppendage) : List UInt8 :=
  encodeUInt 1 (StpCanceledOptionalValue.tag message.stpCanceledOptionalValue)
    ++ (StpCanceledOptionalValue.encode message.stpCanceledOptionalValue)

def decodeBody (bytes : List UInt8) : Option (StpCanceledAppendage × List UInt8) := do
  let (stpCanceledOptionalField, bytes) ← decodeUInt 1 bytes
  let (stpCanceledOptionalValue, bytes) ← StpCanceledOptionalValue.decode stpCanceledOptionalField bytes
  pure ({ stpCanceledOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : StpCanceledAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StpCanceledOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : StpCanceledAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.stpCanceledOptionalValue with
  | userRefIdx inner =>
    simp only [StpCanceledOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : StpCanceledAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (StpCanceledAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : StpCanceledAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : StpCanceledAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end StpCanceledAppendage

/-- Stp Canceled Message -/
structure StpCanceledMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  decrementShares : BitVec 32
  cancelReason : Alpha 4
  quantityPreventedFromTrading : BitVec 32
  price : BitVec 64
  liquidityFlag : LiquidityFlag
  stpCanceledAppendage : Sized 2 StpCanceledAppendage.encode
  deriving DecidableEq, Repr

namespace StpCanceledMessage

def encode (message : StpCanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.decrementShares
    ++ (Alpha.encode message.cancelReason
    ++ (encodeUInt 4 message.quantityPreventedFromTrading
    ++ (encodeUInt 8 message.price
    ++ (LiquidityFlag.encode message.liquidityFlag
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany StpCanceledAppendage.encode message.stpCanceledAppendage.val).length)
    ++ (encodeMany StpCanceledAppendage.encode message.stpCanceledAppendage.val))))))))

def decode (bytes : List UInt8) : Option (StpCanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (decrementShares, bytes) ← decodeUInt 4 bytes
  let (cancelReason, bytes) ← Alpha.decode 4 bytes
  let (quantityPreventedFromTrading, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (stpCanceledAppendage_, bytes) ← decodeSized StpCanceledAppendage.decode appendageLength.toNat bytes
  if fits_stpCanceledAppendage : (encodeMany StpCanceledAppendage.encode stpCanceledAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, decrementShares, cancelReason, quantityPreventedFromTrading, price, liquidityFlag, stpCanceledAppendage := ⟨stpCanceledAppendage_, fits_stpCanceledAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : StpCanceledMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StpCanceledMessage) : (encode message).length ≤ 65570 := by
  have bound_stpCanceledAppendage := message.stpCanceledAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LiquidityFlag.encode_length]
  omega

@[simp] theorem decode_encode (message : StpCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 StpCanceledAppendage.encode StpCanceledAppendage.decode StpCanceledAppendage.decode_encode StpCanceledAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.stpCanceledAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : StpCanceledMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end StpCanceledMessage

/-- Execute Match: 1 bytes -/
structure ExecuteMatchValue where
  executeMatch : ExecuteMatch
  deriving DecidableEq, Repr

namespace ExecuteMatchValue

def encode (message : ExecuteMatchValue) : List UInt8 :=
  ExecuteMatch.encode message.executeMatch

def decode (bytes : List UInt8) : Option (ExecuteMatchValue × List UInt8) := do
  let (executeMatch, bytes) ← ExecuteMatch.decode bytes
  pure ({ executeMatch }, bytes)

@[simp] theorem encode_length (message : ExecuteMatchValue) : (encode message).length = 1 := by
  unfold encode
  simp only [ExecuteMatch.encode_length]

theorem encode_length_pos (message : ExecuteMatchValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecuteMatchValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExecuteMatch.decode_encode, some_bind]
  rfl

end ExecuteMatchValue

/-- Secondary Order Id: 8 bytes -/
structure SecondaryOrderIdValue where
  secondaryOrderId : BitVec 64
  deriving DecidableEq, Repr

namespace SecondaryOrderIdValue

def encode (message : SecondaryOrderIdValue) : List UInt8 :=
  encodeUInt 8 message.secondaryOrderId

def decode (bytes : List UInt8) : Option (SecondaryOrderIdValue × List UInt8) := do
  let (secondaryOrderId, bytes) ← decodeUInt 8 bytes
  pure ({ secondaryOrderId }, bytes)

@[simp] theorem encode_length (message : SecondaryOrderIdValue) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondaryOrderIdValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondaryOrderIdValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondaryOrderIdValue

/-- Broker Pref: 1 bytes -/
structure BrokerPrefValue where
  brokerPref : BrokerPref
  deriving DecidableEq, Repr

namespace BrokerPrefValue

def encode (message : BrokerPrefValue) : List UInt8 :=
  BrokerPref.encode message.brokerPref

def decode (bytes : List UInt8) : Option (BrokerPrefValue × List UInt8) := do
  let (brokerPref, bytes) ← BrokerPref.decode bytes
  pure ({ brokerPref }, bytes)

@[simp] theorem encode_length (message : BrokerPrefValue) : (encode message).length = 1 := by
  unfold encode
  simp only [BrokerPref.encode_length]

theorem encode_length_pos (message : BrokerPrefValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokerPrefValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [BrokerPref.decode_encode, some_bind]
  rfl

end BrokerPrefValue

/-- Principal Trade: 1 bytes -/
structure PrincipalTradeValue where
  principalTrade : PrincipalTrade
  deriving DecidableEq, Repr

namespace PrincipalTradeValue

def encode (message : PrincipalTradeValue) : List UInt8 :=
  PrincipalTrade.encode message.principalTrade

def decode (bytes : List UInt8) : Option (PrincipalTradeValue × List UInt8) := do
  let (principalTrade, bytes) ← PrincipalTrade.decode bytes
  pure ({ principalTrade }, bytes)

@[simp] theorem encode_length (message : PrincipalTradeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [PrincipalTrade.encode_length]

theorem encode_length_pos (message : PrincipalTradeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PrincipalTradeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PrincipalTrade.decode_encode, some_bind]
  rfl

end PrincipalTradeValue

/-- Wash Trade: 1 bytes -/
structure WashTradeValue where
  washTrade : WashTrade
  deriving DecidableEq, Repr

namespace WashTradeValue

def encode (message : WashTradeValue) : List UInt8 :=
  WashTrade.encode message.washTrade

def decode (bytes : List UInt8) : Option (WashTradeValue × List UInt8) := do
  let (washTrade, bytes) ← WashTrade.decode bytes
  pure ({ washTrade }, bytes)

@[simp] theorem encode_length (message : WashTradeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [WashTrade.encode_length]

theorem encode_length_pos (message : WashTradeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WashTradeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [WashTrade.decode_encode, some_bind]
  rfl

end WashTradeValue

/-- Cum Rate: 2 bytes -/
structure CumRateValue where
  cumRate : BitVec 16
  deriving DecidableEq, Repr

namespace CumRateValue

def encode (message : CumRateValue) : List UInt8 :=
  encodeUInt 2 message.cumRate

def decode (bytes : List UInt8) : Option (CumRateValue × List UInt8) := do
  let (cumRate, bytes) ← decodeUInt 2 bytes
  pure ({ cumRate }, bytes)

@[simp] theorem encode_length (message : CumRateValue) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : CumRateValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CumRateValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CumRateValue

/-- Any Order Executed Optional Value, selected by Order Executed Optional Field -/
inductive OrderExecutedOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  | executeMatch (message : ExecuteMatchValue) -- 38
  | secondaryOrderId (message : SecondaryOrderIdValue) -- 40
  | brokerPref (message : BrokerPrefValue) -- 42
  | principalTrade (message : PrincipalTradeValue) -- 13
  | washTrade (message : WashTradeValue) -- 41
  | cumRate (message : CumRateValue) -- 36
  deriving DecidableEq, Repr

namespace OrderExecutedOptionalValue

/-- The Order Executed Optional Field each message is sent under -/
def tag : OrderExecutedOptionalValue → BitVec 8
  | .userRefIdx _ => 37
  | .executeMatch _ => 38
  | .secondaryOrderId _ => 40
  | .brokerPref _ => 42
  | .principalTrade _ => 13
  | .washTrade _ => 41
  | .cumRate _ => 36

def encode : OrderExecutedOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message
  | .executeMatch message => ExecuteMatchValue.encode message
  | .secondaryOrderId message => SecondaryOrderIdValue.encode message
  | .brokerPref message => BrokerPrefValue.encode message
  | .principalTrade message => PrincipalTradeValue.encode message
  | .washTrade message => WashTradeValue.encode message
  | .cumRate message => CumRateValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderExecutedOptionalValue) : (encode message).length ≤ 8 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega
  | executeMatch inner =>
    simp only [encode, ExecuteMatchValue.encode_length]
    omega
  | secondaryOrderId inner =>
    simp only [encode, SecondaryOrderIdValue.encode_length]
    omega
  | brokerPref inner =>
    simp only [encode, BrokerPrefValue.encode_length]
    omega
  | principalTrade inner =>
    simp only [encode, PrincipalTradeValue.encode_length]
    omega
  | washTrade inner =>
    simp only [encode, WashTradeValue.encode_length]
    omega
  | cumRate inner =>
    simp only [encode, CumRateValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderExecutedOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else if tag = 38 then (ExecuteMatchValue.decode bytes).map fun (message, rest) => (.executeMatch message, rest)
  else if tag = 40 then (SecondaryOrderIdValue.decode bytes).map fun (message, rest) => (.secondaryOrderId message, rest)
  else if tag = 42 then (BrokerPrefValue.decode bytes).map fun (message, rest) => (.brokerPref message, rest)
  else if tag = 13 then (PrincipalTradeValue.decode bytes).map fun (message, rest) => (.principalTrade message, rest)
  else if tag = 41 then (WashTradeValue.decode bytes).map fun (message, rest) => (.washTrade message, rest)
  else if tag = 36 then (CumRateValue.decode bytes).map fun (message, rest) => (.cumRate message, rest)
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
  | executeMatch inner =>
    simp only [OrderExecutedOptionalValue.encode, List.length_append, encodeUInt_length, ExecuteMatchValue.encode_length]
    omega
  | secondaryOrderId inner =>
    simp only [OrderExecutedOptionalValue.encode, List.length_append, encodeUInt_length, SecondaryOrderIdValue.encode_length]
    omega
  | brokerPref inner =>
    simp only [OrderExecutedOptionalValue.encode, List.length_append, encodeUInt_length, BrokerPrefValue.encode_length]
    omega
  | principalTrade inner =>
    simp only [OrderExecutedOptionalValue.encode, List.length_append, encodeUInt_length, PrincipalTradeValue.encode_length]
    omega
  | washTrade inner =>
    simp only [OrderExecutedOptionalValue.encode, List.length_append, encodeUInt_length, WashTradeValue.encode_length]
    omega
  | cumRate inner =>
    simp only [OrderExecutedOptionalValue.encode, List.length_append, encodeUInt_length, CumRateValue.encode_length]
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
  execBroker : ExecBroker
  contraBroker : BitVec 32
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
    ++ (ExecBroker.encode message.execBroker
    ++ (encodeUInt 4 message.contraBroker
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderExecutedAppendage.encode message.orderExecutedAppendage.val).length)
    ++ (encodeMany OrderExecutedAppendage.encode message.orderExecutedAppendage.val)))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (liquidityFlag, bytes) ← LiquidityFlag.decode bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (execBroker, bytes) ← ExecBroker.decode bytes
  let (contraBroker, bytes) ← decodeUInt 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (orderExecutedAppendage_, bytes) ← decodeSized OrderExecutedAppendage.decode appendageLength.toNat bytes
  if fits_orderExecutedAppendage : (encodeMany OrderExecutedAppendage.encode orderExecutedAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, quantity, price, liquidityFlag, matchNumber, execBroker, contraBroker, orderExecutedAppendage := ⟨orderExecutedAppendage_, fits_orderExecutedAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecutedMessage) : (encode message).length ≤ 65575 := by
  have bound_orderExecutedAppendage := message.orderExecutedAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, LiquidityFlag.encode_length, ExecBroker.encode_length]
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
  rw [List.append_assoc, ExecBroker.decode_encode, some_bind]
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

/-- Any Corrected Trade Optional Value, selected by Corrected Trade Optional Field -/
inductive CorrectedTradeOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  deriving DecidableEq, Repr

namespace CorrectedTradeOptionalValue

/-- The Corrected Trade Optional Field each message is sent under -/
def tag : CorrectedTradeOptionalValue → BitVec 8
  | .userRefIdx _ => 37

def encode : CorrectedTradeOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CorrectedTradeOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CorrectedTradeOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : CorrectedTradeOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CorrectedTradeOptionalValue

/-- Corrected Trade Appendage -/
structure CorrectedTradeAppendage where
  correctedTradeOptionalValue : CorrectedTradeOptionalValue
  deriving DecidableEq, Repr

namespace CorrectedTradeAppendage

def encodeBody (message : CorrectedTradeAppendage) : List UInt8 :=
  encodeUInt 1 (CorrectedTradeOptionalValue.tag message.correctedTradeOptionalValue)
    ++ (CorrectedTradeOptionalValue.encode message.correctedTradeOptionalValue)

def decodeBody (bytes : List UInt8) : Option (CorrectedTradeAppendage × List UInt8) := do
  let (correctedTradeOptionalField, bytes) ← decodeUInt 1 bytes
  let (correctedTradeOptionalValue, bytes) ← CorrectedTradeOptionalValue.decode correctedTradeOptionalField bytes
  pure ({ correctedTradeOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : CorrectedTradeAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CorrectedTradeOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : CorrectedTradeAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.correctedTradeOptionalValue with
  | userRefIdx inner =>
    simp only [CorrectedTradeOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : CorrectedTradeAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (CorrectedTradeAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : CorrectedTradeAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : CorrectedTradeAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end CorrectedTradeAppendage

/-- Corrected Trade Message -/
structure CorrectedTradeMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  matchNumber : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  correctedTradeAppendage : Sized 2 CorrectedTradeAppendage.encode
  deriving DecidableEq, Repr

namespace CorrectedTradeMessage

def encode (message : CorrectedTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 8 message.matchNumber
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany CorrectedTradeAppendage.encode message.correctedTradeAppendage.val).length)
    ++ (encodeMany CorrectedTradeAppendage.encode message.correctedTradeAppendage.val))))))

def decode (bytes : List UInt8) : Option (CorrectedTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (correctedTradeAppendage_, bytes) ← decodeSized CorrectedTradeAppendage.decode appendageLength.toNat bytes
  if fits_correctedTradeAppendage : (encodeMany CorrectedTradeAppendage.encode correctedTradeAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, matchNumber, quantity, price, correctedTradeAppendage := ⟨correctedTradeAppendage_, fits_correctedTradeAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : CorrectedTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CorrectedTradeMessage) : (encode message).length ≤ 65569 := by
  have bound_correctedTradeAppendage := message.correctedTradeAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : CorrectedTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 CorrectedTradeAppendage.encode CorrectedTradeAppendage.decode CorrectedTradeAppendage.decode_encode CorrectedTradeAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.correctedTradeAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CorrectedTradeMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CorrectedTradeMessage

/-- Any Rejected Order Optional Value, selected by Rejected Order Optional Field -/
inductive RejectedOrderOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  deriving DecidableEq, Repr

namespace RejectedOrderOptionalValue

/-- The Rejected Order Optional Field each message is sent under -/
def tag : RejectedOrderOptionalValue → BitVec 8
  | .userRefIdx _ => 37

def encode : RejectedOrderOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : RejectedOrderOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (RejectedOrderOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
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
  rejectReason : Alpha 4
  rejectedOrderAppendage : Sized 2 RejectedOrderAppendage.encode
  deriving DecidableEq, Repr

namespace RejectedOrderMessage

def encode (message : RejectedOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.rejectReason
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany RejectedOrderAppendage.encode message.rejectedOrderAppendage.val).length)
    ++ (encodeMany RejectedOrderAppendage.encode message.rejectedOrderAppendage.val))))

def decode (bytes : List UInt8) : Option (RejectedOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (rejectReason, bytes) ← Alpha.decode 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (rejectedOrderAppendage_, bytes) ← decodeSized RejectedOrderAppendage.decode appendageLength.toNat bytes
  if fits_rejectedOrderAppendage : (encodeMany RejectedOrderAppendage.encode rejectedOrderAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, rejectReason, rejectedOrderAppendage := ⟨rejectedOrderAppendage_, fits_rejectedOrderAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : RejectedOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RejectedOrderMessage) : (encode message).length ≤ 65553 := by
  have bound_rejectedOrderAppendage := message.rejectedOrderAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : RejectedOrderMessage) (rest : List UInt8) :
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
  rw [decodeSized_encodeMany 2 RejectedOrderAppendage.encode RejectedOrderAppendage.decode RejectedOrderAppendage.decode_encode RejectedOrderAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.rejectedOrderAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RejectedOrderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RejectedOrderMessage

/-- Any Cancel Reject Optional Value, selected by Cancel Reject Optional Field -/
inductive CancelRejectOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  deriving DecidableEq, Repr

namespace CancelRejectOptionalValue

/-- The Cancel Reject Optional Field each message is sent under -/
def tag : CancelRejectOptionalValue → BitVec 8
  | .userRefIdx _ => 37

def encode : CancelRejectOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CancelRejectOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CancelRejectOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
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
  rejectReason : Alpha 4
  cancelRejectAppendage : Sized 2 CancelRejectAppendage.encode
  deriving DecidableEq, Repr

namespace CancelRejectMessage

def encode (message : CancelRejectMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.rejectReason
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany CancelRejectAppendage.encode message.cancelRejectAppendage.val).length)
    ++ (encodeMany CancelRejectAppendage.encode message.cancelRejectAppendage.val))))

def decode (bytes : List UInt8) : Option (CancelRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (rejectReason, bytes) ← Alpha.decode 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (cancelRejectAppendage_, bytes) ← decodeSized CancelRejectAppendage.decode appendageLength.toNat bytes
  if fits_cancelRejectAppendage : (encodeMany CancelRejectAppendage.encode cancelRejectAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, rejectReason, cancelRejectAppendage := ⟨cancelRejectAppendage_, fits_cancelRejectAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : CancelRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CancelRejectMessage) : (encode message).length ≤ 65553 := by
  have bound_cancelRejectAppendage := message.cancelRejectAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : CancelRejectMessage) (rest : List UInt8) :
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
  rw [decodeSized_encodeMany 2 CancelRejectAppendage.encode CancelRejectAppendage.decode CancelRejectAppendage.decode_encode CancelRejectAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.cancelRejectAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CancelRejectMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CancelRejectMessage

/-- Any Order Restated Optional Value, selected by Order Restated Optional Field -/
inductive OrderRestatedOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  | firmUpId (message : FirmUpIdValue) -- 31
  deriving DecidableEq, Repr

namespace OrderRestatedOptionalValue

/-- The Order Restated Optional Field each message is sent under -/
def tag : OrderRestatedOptionalValue → BitVec 8
  | .userRefIdx _ => 37
  | .firmUpId _ => 31

def encode : OrderRestatedOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message
  | .firmUpId message => FirmUpIdValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OrderRestatedOptionalValue) : (encode message).length ≤ 8 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega
  | firmUpId inner =>
    simp only [encode, FirmUpIdValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OrderRestatedOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else if tag = 31 then (FirmUpIdValue.decode bytes).map fun (message, rest) => (.firmUpId message, rest)
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
  | userRefIdx inner =>
    simp only [OrderRestatedOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega
  | firmUpId inner =>
    simp only [OrderRestatedOptionalValue.encode, List.length_append, encodeUInt_length, FirmUpIdValue.encode_length]
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
  restateReason : RestateReason
  orderRestatedAppendage : Sized 2 OrderRestatedAppendage.encode
  deriving DecidableEq, Repr

namespace OrderRestatedMessage

def encode (message : OrderRestatedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (RestateReason.encode message.restateReason
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany OrderRestatedAppendage.encode message.orderRestatedAppendage.val).length)
    ++ (encodeMany OrderRestatedAppendage.encode message.orderRestatedAppendage.val))))

def decode (bytes : List UInt8) : Option (OrderRestatedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (restateReason, bytes) ← RestateReason.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (orderRestatedAppendage_, bytes) ← decodeSized OrderRestatedAppendage.decode appendageLength.toNat bytes
  if fits_orderRestatedAppendage : (encodeMany OrderRestatedAppendage.encode orderRestatedAppendage_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, restateReason, orderRestatedAppendage := ⟨orderRestatedAppendage_, fits_orderRestatedAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderRestatedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderRestatedMessage) : (encode message).length ≤ 65550 := by
  have bound_orderRestatedAppendage := message.orderRestatedAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, RestateReason.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderRestatedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RestateReason.decode_encode, some_bind]
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
  | userRefIdx (message : UserRefIdxValue) -- 37
  deriving DecidableEq, Repr

namespace AccountQueryResponseOptionalValue

/-- The Account Query Response Optional Field each message is sent under -/
def tag : AccountQueryResponseOptionalValue → BitVec 8
  | .userRefIdx _ => 37

def encode : AccountQueryResponseOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AccountQueryResponseOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AccountQueryResponseOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
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

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderAcceptedMessage (message : OrderAcceptedMessage) -- "A" 0x41
  | orderReplacedMessage (message : OrderReplacedMessage) -- "U" 0x55
  | orderCanceledMessage (message : OrderCanceledMessage) -- "C" 0x43
  | stpCanceledMessage (message : StpCanceledMessage) -- "D" 0x44
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | correctedTradeMessage (message : CorrectedTradeMessage) -- "B" 0x42
  | rejectedOrderMessage (message : RejectedOrderMessage) -- "J" 0x4A
  | cancelRejectMessage (message : CancelRejectMessage) -- "I" 0x49
  | orderRestatedMessage (message : OrderRestatedMessage) -- "R" 0x52
  | accountQueryResponseMessage (message : AccountQueryResponseMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .orderAcceptedMessage _ => 65
  | .orderReplacedMessage _ => 85
  | .orderCanceledMessage _ => 67
  | .stpCanceledMessage _ => 68
  | .orderExecutedMessage _ => 69
  | .correctedTradeMessage _ => 66
  | .rejectedOrderMessage _ => 74
  | .cancelRejectMessage _ => 73
  | .orderRestatedMessage _ => 82
  | .accountQueryResponseMessage _ => 81

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderAcceptedMessage message => OrderAcceptedMessage.encode message
  | .orderReplacedMessage message => OrderReplacedMessage.encode message
  | .orderCanceledMessage message => OrderCanceledMessage.encode message
  | .stpCanceledMessage message => StpCanceledMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .correctedTradeMessage message => CorrectedTradeMessage.encode message
  | .rejectedOrderMessage message => RejectedOrderMessage.encode message
  | .cancelRejectMessage message => CancelRejectMessage.encode message
  | .orderRestatedMessage message => OrderRestatedMessage.encode message
  | .accountQueryResponseMessage message => AccountQueryResponseMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option SequencedMessage :=
  if tag = 83 then (SystemEventMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.systemEventMessage message) else none
  else if tag = 65 then (OrderAcceptedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderAcceptedMessage message) else none
  else if tag = 85 then (OrderReplacedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderReplacedMessage message) else none
  else if tag = 67 then (OrderCanceledMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderCanceledMessage message) else none
  else if tag = 68 then (StpCanceledMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.stpCanceledMessage message) else none
  else if tag = 69 then (OrderExecutedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecutedMessage message) else none
  else if tag = 66 then (CorrectedTradeMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.correctedTradeMessage message) else none
  else if tag = 74 then (RejectedOrderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.rejectedOrderMessage message) else none
  else if tag = 73 then (CancelRejectMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.cancelRejectMessage message) else none
  else if tag = 82 then (OrderRestatedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderRestatedMessage message) else none
  else if tag = 81 then (AccountQueryResponseMessage.decode bytes).map fun message => .accountQueryResponseMessage message
  else none

theorem decode_encode (message : SequencedMessage) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | systemEventMessage message => simp [decode, encode, tag, SystemEventMessage.decode_encode_nil]
  | orderAcceptedMessage message => simp [decode, encode, tag, OrderAcceptedMessage.decode_encode_nil]
  | orderReplacedMessage message => simp [decode, encode, tag, OrderReplacedMessage.decode_encode_nil]
  | orderCanceledMessage message => simp [decode, encode, tag, OrderCanceledMessage.decode_encode_nil]
  | stpCanceledMessage message => simp [decode, encode, tag, StpCanceledMessage.decode_encode_nil]
  | orderExecutedMessage message => simp [decode, encode, tag, OrderExecutedMessage.decode_encode_nil]
  | correctedTradeMessage message => simp [decode, encode, tag, CorrectedTradeMessage.decode_encode_nil]
  | rejectedOrderMessage message => simp [decode, encode, tag, RejectedOrderMessage.decode_encode_nil]
  | cancelRejectMessage message => simp [decode, encode, tag, CancelRejectMessage.decode_encode_nil]
  | orderRestatedMessage message => simp [decode, encode, tag, OrderRestatedMessage.decode_encode_nil]
  | accountQueryResponseMessage message => simp [decode, encode, tag, AccountQueryResponseMessage.decode_encode]

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

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNasdaqcanadaOrderentryOuchV5014Server
