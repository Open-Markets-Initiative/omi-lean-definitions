import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nasdaq Canada Order Entry v5.0.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Appendage Length and the Account Query Request Appendage it sizes are there only when bytes remain after Account Query Request Message's fixed fields: they are read as one optional closing field.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Client Soup Bin Tcp Packet's body has no bound its 2 byte Packet Length must fit, so every message carries the proof its own encoding fits: the record is its body with that proof, checked as the frame is read.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNasdaqcanadaOrderentryOuchV5014Client

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

/-- Login Request Packet: 46 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequestPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequestPacket

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

/-- Any Enter Order Optional Value, selected by Enter Order Optional Field -/
inductive EnterOrderOptionalValue where
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
  deriving DecidableEq, Repr

namespace EnterOrderOptionalValue

/-- The Enter Order Optional Field each message is sent under -/
def tag : EnterOrderOptionalValue → BitVec 8
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

def encode : EnterOrderOptionalValue → List UInt8
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

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EnterOrderOptionalValue) : (encode message).length ≤ 52 := by
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (EnterOrderOptionalValue × List UInt8) :=
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
  else none

@[simp] theorem decode_encode (message : EnterOrderOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end EnterOrderOptionalValue

/-- Enter Order Appendage -/
structure EnterOrderAppendage where
  enterOrderOptionalValue : EnterOrderOptionalValue
  deriving DecidableEq, Repr

namespace EnterOrderAppendage

def encodeBody (message : EnterOrderAppendage) : List UInt8 :=
  encodeUInt 1 (EnterOrderOptionalValue.tag message.enterOrderOptionalValue)
    ++ (EnterOrderOptionalValue.encode message.enterOrderOptionalValue)

def decodeBody (bytes : List UInt8) : Option (EnterOrderAppendage × List UInt8) := do
  let (enterOrderOptionalField, bytes) ← decodeUInt 1 bytes
  let (enterOrderOptionalValue, bytes) ← EnterOrderOptionalValue.decode enterOrderOptionalField bytes
  pure ({ enterOrderOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : EnterOrderAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EnterOrderOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : EnterOrderAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.enterOrderOptionalValue with
  | userRefIdx inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega
  | account inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, AccountValue.encode_length]
    omega
  | pegType inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, PegTypeValue.encode_length]
    omega
  | minQtyType inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyTypeValue.encode_length]
    omega
  | minQty inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, MaxFloorValue.encode_length]
    omega
  | expireTime inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, ExpireTimeValue.encode_length]
    omega
  | pegOffset inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, PegOffsetValue.encode_length]
    omega
  | targetStrategy inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, TargetStrategyValue.encode_length]
    omega
  | orderOrigination inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, OrderOriginationValue.encode_length]
    omega
  | routingArrangementIndicator inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, RoutingArrangementIndicatorValue.encode_length]
    omega
  | basketTrade inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, BasketTradeValue.encode_length]
    omega
  | programTrade inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, ProgramTradeValue.encode_length]
    omega
  | jitney inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, JitneyValue.encode_length]
    omega
  | gefEligible inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, GefEligibleValue.encode_length]
    omega
  | anonymous inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, AnonymousValue.encode_length]
    omega
  | umirRegulationId inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, UmirRegulationIdValue.encode_length]
    omega
  | bypass inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, BypassValue.encode_length]
    omega
  | tsxncib inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, TsxncibValue.encode_length]
    omega
  | noTradeFeat inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, NoTradeFeatValue.encode_length]
    omega
  | noTradeKey inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, NoTradeKeyValue.encode_length]
    omega
  | shortMarkingExempt inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, ShortMarkingExemptValue.encode_length]
    omega
  | poComment inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, PoCommentValue.encode_length]
    omega
  | displayRange inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, DisplayRangeValue.encode_length]
    omega
  | customerAccount inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, CustomerAccountValue.encode_length]
    omega
  | algorithmId inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, AlgorithmIdValue.encode_length]
    omega
  | customerLei inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, CustomerLeiValue.encode_length]
    omega
  | brokerLei inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, BrokerLeiValue.encode_length]
    omega
  | conditionalOrder inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, ConditionalOrderValue.encode_length]
    omega
  | allowConditional inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, AllowConditionalValue.encode_length]
    omega
  | firmUpId inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, FirmUpIdValue.encode_length]
    omega
  | cxdConnect inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, CxdConnectValue.encode_length]
    omega
  | pureStreamConnect inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, PureStreamConnectValue.encode_length]
    omega
  | minRate inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, MinRateValue.encode_length]
    omega
  | maxRate inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, MaxRateValue.encode_length]
    omega
  | routingStrategy inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, RoutingStrategyValue.encode_length]
    omega
  | handlInst inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, HandlInstValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : EnterOrderAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (EnterOrderAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : EnterOrderAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : EnterOrderAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end EnterOrderAppendage

/-- Enter Order Message -/
structure EnterOrderMessage where
  userRefNum : BitVec 32
  orderQty : BitVec 32
  price : BitVec 64
  side : Side
  symbol : Alpha 10
  timeInForce : TimeInForce
  exDestination : ExDestination
  umirAccountType : Alpha 2
  umirUserId : Alpha 8
  enterOrderAppendage : Sized 2 EnterOrderAppendage.encode
  deriving DecidableEq, Repr

namespace EnterOrderMessage

def encode (message : EnterOrderMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Side.encode message.side
    ++ (Alpha.encode message.symbol
    ++ (TimeInForce.encode message.timeInForce
    ++ (ExDestination.encode message.exDestination
    ++ (Alpha.encode message.umirAccountType
    ++ (Alpha.encode message.umirUserId
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany EnterOrderAppendage.encode message.enterOrderAppendage.val).length)
    ++ (encodeMany EnterOrderAppendage.encode message.enterOrderAppendage.val))))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (exDestination, bytes) ← ExDestination.decode bytes
  let (umirAccountType, bytes) ← Alpha.decode 2 bytes
  let (umirUserId, bytes) ← Alpha.decode 8 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (enterOrderAppendage_, bytes) ← decodeSized EnterOrderAppendage.decode appendageLength.toNat bytes
  if fits_enterOrderAppendage : (encodeMany EnterOrderAppendage.encode enterOrderAppendage_).length < 256 ^ 2 then
    pure ({ userRefNum, orderQty, price, side, symbol, timeInForce, exDestination, umirAccountType, umirUserId, enterOrderAppendage := ⟨enterOrderAppendage_, fits_enterOrderAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : EnterOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnterOrderMessage) : (encode message).length ≤ 65576 := by
  have bound_enterOrderAppendage := message.enterOrderAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Side.encode_length, Alpha.encode_length, TimeInForce.encode_length, ExDestination.encode_length]
  omega

@[simp] theorem decode_encode (message : EnterOrderMessage) (rest : List UInt8) :
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
  rw [decodeSized_encodeMany 2 EnterOrderAppendage.encode EnterOrderAppendage.decode EnterOrderAppendage.decode_encode EnterOrderAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.enterOrderAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EnterOrderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EnterOrderMessage

/-- Any Replace Order Request Optional Value, selected by Replace Order Request Optional Field -/
inductive ReplaceOrderRequestOptionalValue where
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
  deriving DecidableEq, Repr

namespace ReplaceOrderRequestOptionalValue

/-- The Replace Order Request Optional Field each message is sent under -/
def tag : ReplaceOrderRequestOptionalValue → BitVec 8
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

def encode : ReplaceOrderRequestOptionalValue → List UInt8
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

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ReplaceOrderRequestOptionalValue) : (encode message).length ≤ 52 := by
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ReplaceOrderRequestOptionalValue × List UInt8) :=
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
  else none

@[simp] theorem decode_encode (message : ReplaceOrderRequestOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ReplaceOrderRequestOptionalValue

/-- Replace Order Request Appendage -/
structure ReplaceOrderRequestAppendage where
  replaceOrderRequestOptionalValue : ReplaceOrderRequestOptionalValue
  deriving DecidableEq, Repr

namespace ReplaceOrderRequestAppendage

def encodeBody (message : ReplaceOrderRequestAppendage) : List UInt8 :=
  encodeUInt 1 (ReplaceOrderRequestOptionalValue.tag message.replaceOrderRequestOptionalValue)
    ++ (ReplaceOrderRequestOptionalValue.encode message.replaceOrderRequestOptionalValue)

def decodeBody (bytes : List UInt8) : Option (ReplaceOrderRequestAppendage × List UInt8) := do
  let (replaceOrderRequestOptionalField, bytes) ← decodeUInt 1 bytes
  let (replaceOrderRequestOptionalValue, bytes) ← ReplaceOrderRequestOptionalValue.decode replaceOrderRequestOptionalField bytes
  pure ({ replaceOrderRequestOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : ReplaceOrderRequestAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReplaceOrderRequestOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ReplaceOrderRequestAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.replaceOrderRequestOptionalValue with
  | userRefIdx inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega
  | minQtyType inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyTypeValue.encode_length]
    omega
  | pegType inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, PegTypeValue.encode_length]
    omega
  | minQty inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, MaxFloorValue.encode_length]
    omega
  | expireTime inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, ExpireTimeValue.encode_length]
    omega
  | pegOffset inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, PegOffsetValue.encode_length]
    omega
  | targetStrategy inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, TargetStrategyValue.encode_length]
    omega
  | orderOrigination inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, OrderOriginationValue.encode_length]
    omega
  | routingArrangementIndicator inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, RoutingArrangementIndicatorValue.encode_length]
    omega
  | umirRegulationId inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, UmirRegulationIdValue.encode_length]
    omega
  | anonymous inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, AnonymousValue.encode_length]
    omega
  | displayRange inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, DisplayRangeValue.encode_length]
    omega
  | customerAccount inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, CustomerAccountValue.encode_length]
    omega
  | algorithmId inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, AlgorithmIdValue.encode_length]
    omega
  | customerLei inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, CustomerLeiValue.encode_length]
    omega
  | brokerLei inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, BrokerLeiValue.encode_length]
    omega
  | allowConditional inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, AllowConditionalValue.encode_length]
    omega
  | cxdConnect inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, CxdConnectValue.encode_length]
    omega
  | pureStreamConnect inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, PureStreamConnectValue.encode_length]
    omega
  | minRate inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, MinRateValue.encode_length]
    omega
  | maxRate inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, MaxRateValue.encode_length]
    omega
  | handlInst inner =>
    simp only [ReplaceOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, HandlInstValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ReplaceOrderRequestAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (ReplaceOrderRequestAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : ReplaceOrderRequestAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ReplaceOrderRequestAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ReplaceOrderRequestAppendage

/-- Replace Order Request Message -/
structure ReplaceOrderRequestMessage where
  origUserRefNum : BitVec 32
  userRefNum : BitVec 32
  orderQty : BitVec 32
  price : BitVec 64
  side : Side
  timeInForce : TimeInForce
  replaceOrderRequestAppendage : Sized 2 ReplaceOrderRequestAppendage.encode
  deriving DecidableEq, Repr

namespace ReplaceOrderRequestMessage

def encode (message : ReplaceOrderRequestMessage) : List UInt8 :=
  encodeUInt 4 message.origUserRefNum
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Side.encode message.side
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany ReplaceOrderRequestAppendage.encode message.replaceOrderRequestAppendage.val).length)
    ++ (encodeMany ReplaceOrderRequestAppendage.encode message.replaceOrderRequestAppendage.val)))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderRequestMessage × List UInt8) := do
  let (origUserRefNum, bytes) ← decodeUInt 4 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (replaceOrderRequestAppendage_, bytes) ← decodeSized ReplaceOrderRequestAppendage.decode appendageLength.toNat bytes
  if fits_replaceOrderRequestAppendage : (encodeMany ReplaceOrderRequestAppendage.encode replaceOrderRequestAppendage_).length < 256 ^ 2 then
    pure ({ origUserRefNum, userRefNum, orderQty, price, side, timeInForce, replaceOrderRequestAppendage := ⟨replaceOrderRequestAppendage_, fits_replaceOrderRequestAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReplaceOrderRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReplaceOrderRequestMessage) : (encode message).length ≤ 65559 := by
  have bound_replaceOrderRequestAppendage := message.replaceOrderRequestAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Side.encode_length, TimeInForce.encode_length]
  omega

@[simp] theorem decode_encode (message : ReplaceOrderRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 ReplaceOrderRequestAppendage.encode ReplaceOrderRequestAppendage.decode ReplaceOrderRequestAppendage.decode_encode ReplaceOrderRequestAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.replaceOrderRequestAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReplaceOrderRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReplaceOrderRequestMessage

/-- Any Cancel Order Request Optional Value, selected by Cancel Order Request Optional Field -/
inductive CancelOrderRequestOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  deriving DecidableEq, Repr

namespace CancelOrderRequestOptionalValue

/-- The Cancel Order Request Optional Field each message is sent under -/
def tag : CancelOrderRequestOptionalValue → BitVec 8
  | .userRefIdx _ => 37

def encode : CancelOrderRequestOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CancelOrderRequestOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CancelOrderRequestOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : CancelOrderRequestOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CancelOrderRequestOptionalValue

/-- Cancel Order Request Appendage -/
structure CancelOrderRequestAppendage where
  cancelOrderRequestOptionalValue : CancelOrderRequestOptionalValue
  deriving DecidableEq, Repr

namespace CancelOrderRequestAppendage

def encodeBody (message : CancelOrderRequestAppendage) : List UInt8 :=
  encodeUInt 1 (CancelOrderRequestOptionalValue.tag message.cancelOrderRequestOptionalValue)
    ++ (CancelOrderRequestOptionalValue.encode message.cancelOrderRequestOptionalValue)

def decodeBody (bytes : List UInt8) : Option (CancelOrderRequestAppendage × List UInt8) := do
  let (cancelOrderRequestOptionalField, bytes) ← decodeUInt 1 bytes
  let (cancelOrderRequestOptionalValue, bytes) ← CancelOrderRequestOptionalValue.decode cancelOrderRequestOptionalField bytes
  pure ({ cancelOrderRequestOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : CancelOrderRequestAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CancelOrderRequestOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : CancelOrderRequestAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.cancelOrderRequestOptionalValue with
  | userRefIdx inner =>
    simp only [CancelOrderRequestOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : CancelOrderRequestAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (CancelOrderRequestAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : CancelOrderRequestAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : CancelOrderRequestAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end CancelOrderRequestAppendage

/-- Cancel Order Request Message -/
structure CancelOrderRequestMessage where
  userRefNum : BitVec 32
  orderQty : BitVec 32
  cancelOrderRequestAppendage : Sized 2 CancelOrderRequestAppendage.encode
  deriving DecidableEq, Repr

namespace CancelOrderRequestMessage

def encode (message : CancelOrderRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.orderQty
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany CancelOrderRequestAppendage.encode message.cancelOrderRequestAppendage.val).length)
    ++ (encodeMany CancelOrderRequestAppendage.encode message.cancelOrderRequestAppendage.val)))

def decode (bytes : List UInt8) : Option (CancelOrderRequestMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (cancelOrderRequestAppendage_, bytes) ← decodeSized CancelOrderRequestAppendage.decode appendageLength.toNat bytes
  if fits_cancelOrderRequestAppendage : (encodeMany CancelOrderRequestAppendage.encode cancelOrderRequestAppendage_).length < 256 ^ 2 then
    pure ({ userRefNum, orderQty, cancelOrderRequestAppendage := ⟨cancelOrderRequestAppendage_, fits_cancelOrderRequestAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : CancelOrderRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CancelOrderRequestMessage) : (encode message).length ≤ 65545 := by
  have bound_cancelOrderRequestAppendage := message.cancelOrderRequestAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : CancelOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 CancelOrderRequestAppendage.encode CancelOrderRequestAppendage.decode CancelOrderRequestAppendage.decode_encode CancelOrderRequestAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.cancelOrderRequestAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CancelOrderRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CancelOrderRequestMessage

/-- Any Account Query Request Optional Value, selected by Account Query Request Optional Field -/
inductive AccountQueryRequestOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 37
  deriving DecidableEq, Repr

namespace AccountQueryRequestOptionalValue

/-- The Account Query Request Optional Field each message is sent under -/
def tag : AccountQueryRequestOptionalValue → BitVec 8
  | .userRefIdx _ => 37

def encode : AccountQueryRequestOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AccountQueryRequestOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AccountQueryRequestOptionalValue × List UInt8) :=
  if tag = 37 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : AccountQueryRequestOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AccountQueryRequestOptionalValue

/-- Account Query Request Appendage -/
structure AccountQueryRequestAppendage where
  accountQueryRequestOptionalValue : AccountQueryRequestOptionalValue
  deriving DecidableEq, Repr

namespace AccountQueryRequestAppendage

def encodeBody (message : AccountQueryRequestAppendage) : List UInt8 :=
  encodeUInt 1 (AccountQueryRequestOptionalValue.tag message.accountQueryRequestOptionalValue)
    ++ (AccountQueryRequestOptionalValue.encode message.accountQueryRequestOptionalValue)

def decodeBody (bytes : List UInt8) : Option (AccountQueryRequestAppendage × List UInt8) := do
  let (accountQueryRequestOptionalField, bytes) ← decodeUInt 1 bytes
  let (accountQueryRequestOptionalValue, bytes) ← AccountQueryRequestOptionalValue.decode accountQueryRequestOptionalField bytes
  pure ({ accountQueryRequestOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : AccountQueryRequestAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AccountQueryRequestOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : AccountQueryRequestAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.accountQueryRequestOptionalValue with
  | userRefIdx inner =>
    simp only [AccountQueryRequestOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : AccountQueryRequestAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (AccountQueryRequestAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : AccountQueryRequestAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : AccountQueryRequestAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end AccountQueryRequestAppendage

/-- Account Query Request Message -/
structure AccountQueryRequestMessage where
  accountQueryRequestAppendage : Option (Sized 2 AccountQueryRequestAppendage.encode)
  deriving DecidableEq, Repr

namespace AccountQueryRequestMessage

/-- The Account Query Request Appendage when there: its length, then the entries filling it -/
def encodeAccountQueryRequestAppendage (items : Sized 2 AccountQueryRequestAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany AccountQueryRequestAppendage.encode items.val).length) ++ encodeMany AccountQueryRequestAppendage.encode items.val

def decodeAccountQueryRequestAppendage (bytes : List UInt8) : Option (Sized 2 AccountQueryRequestAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized AccountQueryRequestAppendage.decode length.toNat bytes
  if fits : (encodeMany AccountQueryRequestAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeAccountQueryRequestAppendage_encodeAccountQueryRequestAppendage (items : Sized 2 AccountQueryRequestAppendage.encode) (rest : List UInt8) :
    decodeAccountQueryRequestAppendage (encodeAccountQueryRequestAppendage items ++ rest) = some (items, rest) := by
  unfold decodeAccountQueryRequestAppendage encodeAccountQueryRequestAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 AccountQueryRequestAppendage.encode AccountQueryRequestAppendage.decode AccountQueryRequestAppendage.decode_encode AccountQueryRequestAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeAccountQueryRequestAppendage_length_pos (items : Sized 2 AccountQueryRequestAppendage.encode) : (encodeAccountQueryRequestAppendage items).length > 0 := by
  unfold encodeAccountQueryRequestAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : AccountQueryRequestMessage) : List UInt8 :=
  encodeTail encodeAccountQueryRequestAppendage message.accountQueryRequestAppendage

def decode (bytes : List UInt8) : Option AccountQueryRequestMessage := do
  let accountQueryRequestAppendage ← decodeTail decodeAccountQueryRequestAppendage bytes
  pure { accountQueryRequestAppendage }

theorem decode_encode (message : AccountQueryRequestMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeTail_encodeTail encodeAccountQueryRequestAppendage decodeAccountQueryRequestAppendage decodeAccountQueryRequestAppendage_encodeAccountQueryRequestAppendage encodeAccountQueryRequestAppendage_length_pos, some_bind]
  rfl

end AccountQueryRequestMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrderMessage (message : EnterOrderMessage) -- "O" 0x4F
  | replaceOrderRequestMessage (message : ReplaceOrderRequestMessage) -- "U" 0x55
  | cancelOrderRequestMessage (message : CancelOrderRequestMessage) -- "X" 0x58
  | accountQueryRequestMessage (message : AccountQueryRequestMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrderMessage _ => 79
  | .replaceOrderRequestMessage _ => 85
  | .cancelOrderRequestMessage _ => 88
  | .accountQueryRequestMessage _ => 81

def encode : UnsequencedMessage → List UInt8
  | .enterOrderMessage message => EnterOrderMessage.encode message
  | .replaceOrderRequestMessage message => ReplaceOrderRequestMessage.encode message
  | .cancelOrderRequestMessage message => CancelOrderRequestMessage.encode message
  | .accountQueryRequestMessage message => AccountQueryRequestMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option UnsequencedMessage :=
  if tag = 79 then (EnterOrderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.enterOrderMessage message) else none
  else if tag = 85 then (ReplaceOrderRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.replaceOrderRequestMessage message) else none
  else if tag = 88 then (CancelOrderRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.cancelOrderRequestMessage message) else none
  else if tag = 81 then (AccountQueryRequestMessage.decode bytes).map fun message => .accountQueryRequestMessage message
  else none

theorem decode_encode (message : UnsequencedMessage) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | enterOrderMessage message => simp [decode, encode, tag, EnterOrderMessage.decode_encode_nil]
  | replaceOrderRequestMessage message => simp [decode, encode, tag, ReplaceOrderRequestMessage.decode_encode_nil]
  | cancelOrderRequestMessage message => simp [decode, encode, tag, CancelOrderRequestMessage.decode_encode_nil]
  | accountQueryRequestMessage message => simp [decode, encode, tag, AccountQueryRequestMessage.decode_encode]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option UnsequencedDataPacket := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let unsequencedMessage ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure { unsequencedMessage }

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

theorem decode_encode (message : UnsequencedDataPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end UnsequencedDataPacket

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Logout Request: 0 bytes -/
structure LogoutRequest where
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (_ : LogoutRequest) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogoutRequest

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | clientHeartbeat (message : ClientHeartbeat) -- "R" 0x52
  | logoutRequest (message : LogoutRequest) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeat _ => 82
  | .logoutRequest _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .logoutRequest message => LogoutRequest.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ClientPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 76 then (LoginRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequestPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun message => .unsequencedDataPacket message
  else if tag = 82 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 79 then (LogoutRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutRequest message) else none
  else none

theorem decode_encode (message : ClientPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginRequestPacket message => simp [decode, encode, tag, LoginRequestPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode_nil]

end ClientPayload

/-- Client Soup Bin Tcp Packet: the body, which the record carries with the proof it fits its frame -/
structure ClientSoupBinTcpPacketBody where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacketBody

def encodeBody (message : ClientSoupBinTcpPacketBody) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option ClientSoupBinTcpPacketBody := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let clientPayload ← ClientPayload.decode clientPacketType bytes
  pure { clientPayload }

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacketBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

end ClientSoupBinTcpPacketBody

/-- Client Soup Bin Tcp Packet: the body with the proof its encoding fits Packet Length, whose 2 bytes no bound of the fields fits -/
abbrev ClientSoupBinTcpPacket := Fitting ClientSoupBinTcpPacketBody.encodeBody 0 65536

namespace ClientSoupBinTcpPacket

def encode (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeFramed 2 0 ClientSoupBinTcpPacketBody.encodeBody message.val

def decode : List UInt8 → Option (ClientSoupBinTcpPacket × List UInt8) :=
  decodeFittingAll 2 0 ClientSoupBinTcpPacketBody.encodeBody ClientSoupBinTcpPacketBody.decodeBody

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAll_encodeFramed 2 0 ClientSoupBinTcpPacketBody.encodeBody ClientSoupBinTcpPacketBody.decodeBody message (ClientSoupBinTcpPacketBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ClientSoupBinTcpPacket) : (encode message).length ≤ 65537 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Packet -/
structure ClientPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNasdaqcanadaOrderentryOuchV5014Client
