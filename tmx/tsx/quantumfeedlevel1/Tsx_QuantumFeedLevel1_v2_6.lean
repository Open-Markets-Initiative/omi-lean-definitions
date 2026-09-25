import Omi.Wire

/-!
# TMX Group Quantum Feed Level 1 v2.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Packet's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxTsxQuantumfeedlevel1XmtV26

/-- Protocol Name: one byte code -/
def ProtocolName.codes : List UInt8 :=
  [0x58]

inductive ProtocolName where
  | xmt -- Xmt
  | unlisted (byte : { byte : UInt8 // byte ∉ ProtocolName.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProtocolName

def toByte : ProtocolName → UInt8
  | .xmt => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ProtocolName :=
  .xmt

def ofByte (byte : UInt8) : ProtocolName :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProtocolName) : ofByte value.toByte = value := by
  cases value with
  | xmt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProtocolName) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProtocolName × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProtocolName) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ProtocolName) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProtocolName

/-- Ack Required Poss Dup: one byte code -/
def AckRequiredPossDup.codes : List UInt8 :=
  [0x30]

inductive AckRequiredPossDup where
  | unused -- Unused
  | unlisted (byte : { byte : UInt8 // byte ∉ AckRequiredPossDup.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AckRequiredPossDup

def toByte : AckRequiredPossDup → UInt8
  | .unused => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AckRequiredPossDup :=
  .unused

def ofByte (byte : UInt8) : AckRequiredPossDup :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AckRequiredPossDup) : ofByte value.toByte = value := by
  cases value with
  | unused => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AckRequiredPossDup) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AckRequiredPossDup × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AckRequiredPossDup) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AckRequiredPossDup) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AckRequiredPossDup

/-- Currency: one byte code -/
def Currency.codes : List UInt8 :=
  [0x55, 0x43]

inductive Currency where
  | usd -- Usd
  | cad -- Cad
  | unlisted (byte : { byte : UInt8 // byte ∉ Currency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Currency

def toByte : Currency → UInt8
  | .usd => 0x55
  | .cad => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Currency :=
  if byte = 0x55 then .usd
  else .cad

def ofByte (byte : UInt8) : Currency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Currency) : ofByte value.toByte = value := by
  cases value with
  | usd => decide
  | cad => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Currency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Currency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Currency) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Currency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Currency

/-- Listing Market: one byte code -/
def ListingMarket.codes : List UInt8 :=
  [0x54, 0x56, 0x4E, 0x51, 0x53, 0x4D, 0x58]

inductive ListingMarket where
  | tsx -- Tsx
  | tsxVenture -- Tsx Venture
  | tsxNaVex -- Tsx Na Vex
  | nasdaq -- Nasdaq
  | nyse -- Nyse
  | nyseMkt -- Nyse Mkt
  | nNoMarket -- N No Market
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .tsx => 0x54
  | .tsxVenture => 0x56
  | .tsxNaVex => 0x4E
  | .nasdaq => 0x51
  | .nyse => 0x53
  | .nyseMkt => 0x4D
  | .nNoMarket => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x54 then .tsx
  else if byte = 0x56 then .tsxVenture
  else if byte = 0x4E then .tsxNaVex
  else if byte = 0x51 then .nasdaq
  else if byte = 0x53 then .nyse
  else if byte = 0x4D then .nyseMkt
  else .nNoMarket

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | tsx => decide
  | tsxVenture => decide
  | tsxNaVex => decide
  | nasdaq => decide
  | nyse => decide
  | nyseMkt => decide
  | nNoMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListingMarket) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListingMarket × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListingMarket) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListingMarket) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListingMarket

/-- Product Type: one byte code -/
def ProductType.codes : List UInt8 :=
  [0x42, 0x45, 0x4D, 0x46, 0x55, 0x4F]

inductive ProductType where
  | debenture -- Debenture
  | equity -- Equity
  | mutualFund -- Mutual Fund
  | etf -- Etf
  | usEquity -- Us Equity
  | bond -- Bond
  | unlisted (byte : { byte : UInt8 // byte ∉ ProductType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProductType

def toByte : ProductType → UInt8
  | .debenture => 0x42
  | .equity => 0x45
  | .mutualFund => 0x4D
  | .etf => 0x46
  | .usEquity => 0x55
  | .bond => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProductType :=
  if byte = 0x42 then .debenture
  else if byte = 0x45 then .equity
  else if byte = 0x4D then .mutualFund
  else if byte = 0x46 then .etf
  else if byte = 0x55 then .usEquity
  else .bond

def ofByte (byte : UInt8) : ProductType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProductType) : ofByte value.toByte = value := by
  cases value with
  | debenture => decide
  | equity => decide
  | mutualFund => decide
  | etf => decide
  | usEquity => decide
  | bond => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProductType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProductType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProductType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ProductType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProductType

/-- Test Symbol: one byte code -/
def TestSymbol.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TestSymbol where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TestSymbol.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TestSymbol

def toByte : TestSymbol → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TestSymbol :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : TestSymbol :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TestSymbol) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TestSymbol) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TestSymbol × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TestSymbol) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TestSymbol) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TestSymbol

/-- Moc Eligible: one byte code -/
def MocEligible.codes : List UInt8 :=
  [0x59, 0x4E]

inductive MocEligible where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ MocEligible.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MocEligible

def toByte : MocEligible → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MocEligible :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : MocEligible :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MocEligible) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MocEligible) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MocEligible × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MocEligible) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MocEligible) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MocEligible

/-- Bypass: one byte code -/
def Bypass.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Bypass where
  | theOrderIsABypass -- The Order Is A Bypass
  | theOrderIsNotABypass -- The Order Is Not A Bypass
  | unlisted (byte : { byte : UInt8 // byte ∉ Bypass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Bypass

def toByte : Bypass → UInt8
  | .theOrderIsABypass => 0x59
  | .theOrderIsNotABypass => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Bypass :=
  if byte = 0x59 then .theOrderIsABypass
  else .theOrderIsNotABypass

def ofByte (byte : UInt8) : Bypass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Bypass) : ofByte value.toByte = value := by
  cases value with
  | theOrderIsABypass => decide
  | theOrderIsNotABypass => decide
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

/-- Settlement Terms: one byte code -/
def SettlementTerms.codes : List UInt8 :=
  [0x43, 0x4E, 0x4D, 0x54, 0x44, 0x20]

inductive SettlementTerms where
  | cash -- Cash
  | nn -- Nn
  | ms -- Ms
  | ct -- Ct
  | validSettlementDate -- Valid Settlement Date
  | noSettlementTerms -- No Settlement Terms
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementTerms.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementTerms

def toByte : SettlementTerms → UInt8
  | .cash => 0x43
  | .nn => 0x4E
  | .ms => 0x4D
  | .ct => 0x54
  | .validSettlementDate => 0x44
  | .noSettlementTerms => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementTerms :=
  if byte = 0x43 then .cash
  else if byte = 0x4E then .nn
  else if byte = 0x4D then .ms
  else if byte = 0x54 then .ct
  else if byte = 0x44 then .validSettlementDate
  else .noSettlementTerms

def ofByte (byte : UInt8) : SettlementTerms :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementTerms) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | nn => decide
  | ms => decide
  | ct => decide
  | validSettlementDate => decide
  | noSettlementTerms => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementTerms) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementTerms × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementTerms) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementTerms) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementTerms

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x49, 0x42, 0x43, 0x44, 0x52, 0x53, 0x56, 0x20]

inductive CrossType where
  | internal -- Internal
  | basis -- Basis
  | contingent -- Contingent
  | derivativeRelated -- Derivative Related
  | regular -- Regular
  | specialTradingSession -- Special Trading Session
  | volumeWeightedAveragePrice -- Volume Weighted Average Price
  | defaultTradeWasNotACross -- Default Trade Was Not A Cross
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .internal => 0x49
  | .basis => 0x42
  | .contingent => 0x43
  | .derivativeRelated => 0x44
  | .regular => 0x52
  | .specialTradingSession => 0x53
  | .volumeWeightedAveragePrice => 0x56
  | .defaultTradeWasNotACross => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x49 then .internal
  else if byte = 0x42 then .basis
  else if byte = 0x43 then .contingent
  else if byte = 0x44 then .derivativeRelated
  else if byte = 0x52 then .regular
  else if byte = 0x53 then .specialTradingSession
  else if byte = 0x56 then .volumeWeightedAveragePrice
  else .defaultTradeWasNotACross

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | internal => decide
  | basis => decide
  | contingent => decide
  | derivativeRelated => decide
  | regular => decide
  | specialTradingSession => decide
  | volumeWeightedAveragePrice => decide
  | defaultTradeWasNotACross => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Opening Trade: one byte code -/
def OpeningTrade.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OpeningTrade where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningTrade

def toByte : OpeningTrade → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningTrade :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : OpeningTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningTrade) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningTrade) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpeningTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningTrade

/-- Is Mid Only: one byte code -/
def IsMidOnly.codes : List UInt8 :=
  [0x59, 0x4E]

inductive IsMidOnly where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ IsMidOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsMidOnly

def toByte : IsMidOnly → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IsMidOnly :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : IsMidOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsMidOnly) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsMidOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsMidOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsMidOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IsMidOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsMidOnly

/-- Is Dark: one byte code -/
def IsDark.codes : List UInt8 :=
  [0x59, 0x4E]

inductive IsDark where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ IsDark.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsDark

def toByte : IsDark → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IsDark :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : IsDark :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsDark) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsDark) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsDark × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsDark) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IsDark) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsDark

/-- Is Conditional: one byte code -/
def IsConditional.codes : List UInt8 :=
  [0x59, 0x4E]

inductive IsConditional where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ IsConditional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsConditional

def toByte : IsConditional → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IsConditional :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : IsConditional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsConditional) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsConditional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsConditional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsConditional) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IsConditional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsConditional

/-- Imbalance Side: one byte code -/
def ImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive ImbalanceSide where
  | buy -- Buy
  | sell -- Sell
  | noImbalanceExists -- No Imbalance Exists
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceSide

def toByte : ImbalanceSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .noImbalanceExists => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .noImbalanceExists

def ofByte (byte : UInt8) : ImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | noImbalanceExists => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceSide

/-- Market Order Imbalance Side: one byte code -/
def MarketOrderImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive MarketOrderImbalanceSide where
  | buy -- Buy
  | sell -- Sell
  | noImbalanceExists -- No Imbalance Exists
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketOrderImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketOrderImbalanceSide

def toByte : MarketOrderImbalanceSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .noImbalanceExists => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketOrderImbalanceSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .noImbalanceExists

def ofByte (byte : UInt8) : MarketOrderImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketOrderImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | noImbalanceExists => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketOrderImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketOrderImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketOrderImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketOrderImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketOrderImbalanceSide

/-- Business Header: 9 bytes -/
structure BusinessHeader where
  msgVersion : BitVec 8
  sourceId : Alpha 1
  streamId : BitVec 16
  sequence0 : BitVec 8
  sequence1 : BitVec 32
  deriving DecidableEq, Repr

namespace BusinessHeader

def encode (message : BusinessHeader) : List UInt8 :=
  encodeUInt 1 message.msgVersion
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 1 message.sequence0
    ++ (encodeUIntLE 4 message.sequence1))))

def decode (bytes : List UInt8) : Option (BusinessHeader × List UInt8) := do
  let (msgVersion, bytes) ← decodeUInt 1 bytes
  let (sourceId, bytes) ← Alpha.decode 1 bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (sequence0, bytes) ← decodeUIntLE 1 bytes
  let (sequence1, bytes) ← decodeUIntLE 4 bytes
  pure ({ msgVersion, sourceId, streamId, sequence0, sequence1 }, bytes)

@[simp] theorem encode_length (message : BusinessHeader) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BusinessHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BusinessHeader

/-- Symbol Status Message: 66 bytes -/
structure SymbolStatusMessage where
  symbol : Alpha 12
  stockGroup : BitVec 8
  cusip : Alpha 12
  boardLot : BitVec 16
  currency : Currency
  faceValue : BitVec 64
  lastSalePrice : BitVec 64
  listingMarket : ListingMarket
  productType : ProductType
  buyMaximumQuantity : BitVec 32
  buyMinimumQuantity : BitVec 32
  sellMaximumQuantity : BitVec 32
  sellMinimumQuantity : BitVec 32
  stockState : Alpha 2
  testSymbol : TestSymbol
  mocEligible : MocEligible
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 1 message.stockGroup
    ++ (Alpha.encode message.cusip
    ++ (encodeUIntLE 2 message.boardLot
    ++ (Currency.encode message.currency
    ++ (encodeUIntLE 8 message.faceValue
    ++ (encodeUIntLE 8 message.lastSalePrice
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType
    ++ (encodeUIntLE 4 message.buyMaximumQuantity
    ++ (encodeUIntLE 4 message.buyMinimumQuantity
    ++ (encodeUIntLE 4 message.sellMaximumQuantity
    ++ (encodeUIntLE 4 message.sellMinimumQuantity
    ++ (Alpha.encode message.stockState
    ++ (TestSymbol.encode message.testSymbol
    ++ (MocEligible.encode message.mocEligible)))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (stockGroup, bytes) ← decodeUIntLE 1 bytes
  let (cusip, bytes) ← Alpha.decode 12 bytes
  let (boardLot, bytes) ← decodeUIntLE 2 bytes
  let (currency, bytes) ← Currency.decode bytes
  let (faceValue, bytes) ← decodeUIntLE 8 bytes
  let (lastSalePrice, bytes) ← decodeUIntLE 8 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (buyMaximumQuantity, bytes) ← decodeUIntLE 4 bytes
  let (buyMinimumQuantity, bytes) ← decodeUIntLE 4 bytes
  let (sellMaximumQuantity, bytes) ← decodeUIntLE 4 bytes
  let (sellMinimumQuantity, bytes) ← decodeUIntLE 4 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (testSymbol, bytes) ← TestSymbol.decode bytes
  let (mocEligible, bytes) ← MocEligible.decode bytes
  pure ({ symbol, stockGroup, cusip, boardLot, currency, faceValue, lastSalePrice, listingMarket, productType, buyMaximumQuantity, buyMinimumQuantity, sellMaximumQuantity, sellMinimumQuantity, stockState, testSymbol, mocEligible }, bytes)

@[simp] theorem encode_length (message : SymbolStatusMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, Currency.encode_length, ListingMarket.encode_length, ProductType.encode_length, TestSymbol.encode_length, MocEligible.encode_length]

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Currency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
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
  rw [List.append_assoc, TestSymbol.decode_encode, some_bind]
  dsimp only
  rw [MocEligible.decode_encode, some_bind]
  rfl

end SymbolStatusMessage

/-- Trade Report Message: 57 bytes -/
structure TradeReportMessage where
  symbol : Alpha 12
  price : BitVec 64
  volume : BitVec 32
  buyBrokerNumber : BitVec 16
  sellBrokerNumber : BitVec 16
  bypass : Bypass
  tradeTimeStamp : BitVec 32
  settlementTerms : SettlementTerms
  crossType : CrossType
  lastSalePrice : BitVec 64
  openingTrade : OpeningTrade
  listingMarket : ListingMarket
  productType : ProductType
  tradeNumber : BitVec 32
  tradeDate : BitVec 32
  isMidOnly : IsMidOnly
  isDark : IsDark
  isConditional : IsConditional
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 2 message.buyBrokerNumber
    ++ (encodeUIntLE 2 message.sellBrokerNumber
    ++ (Bypass.encode message.bypass
    ++ (encodeUIntLE 4 message.tradeTimeStamp
    ++ (SettlementTerms.encode message.settlementTerms
    ++ (CrossType.encode message.crossType
    ++ (encodeUIntLE 8 message.lastSalePrice
    ++ (OpeningTrade.encode message.openingTrade
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (IsMidOnly.encode message.isMidOnly
    ++ (IsDark.encode message.isDark
    ++ (IsConditional.encode message.isConditional)))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (buyBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (sellBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (bypass, bytes) ← Bypass.decode bytes
  let (tradeTimeStamp, bytes) ← decodeUIntLE 4 bytes
  let (settlementTerms, bytes) ← SettlementTerms.decode bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (lastSalePrice, bytes) ← decodeUIntLE 8 bytes
  let (openingTrade, bytes) ← OpeningTrade.decode bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (isMidOnly, bytes) ← IsMidOnly.decode bytes
  let (isDark, bytes) ← IsDark.decode bytes
  let (isConditional, bytes) ← IsConditional.decode bytes
  pure ({ symbol, price, volume, buyBrokerNumber, sellBrokerNumber, bypass, tradeTimeStamp, settlementTerms, crossType, lastSalePrice, openingTrade, listingMarket, productType, tradeNumber, tradeDate, isMidOnly, isDark, isConditional }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, Bypass.encode_length, SettlementTerms.encode_length, CrossType.encode_length, OpeningTrade.encode_length, ListingMarket.encode_length, ProductType.encode_length, IsMidOnly.encode_length, IsDark.encode_length, IsConditional.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Bypass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementTerms.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, IsMidOnly.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IsDark.decode_encode, some_bind]
  dsimp only
  rw [IsConditional.decode_encode, some_bind]
  rfl

end TradeReportMessage

/-- Trade Cancelled Message: 50 bytes -/
structure TradeCancelledMessage where
  symbol : Alpha 12
  price : BitVec 64
  volume : BitVec 32
  buyBrokerNumber : BitVec 16
  sellBrokerNumber : BitVec 16
  tradeTimeStamp : BitVec 32
  lastSalePrice : BitVec 64
  listingMarket : ListingMarket
  productType : ProductType
  tradeNumber : BitVec 32
  tradeDate : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancelledMessage

def encode (message : TradeCancelledMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 2 message.buyBrokerNumber
    ++ (encodeUIntLE 2 message.sellBrokerNumber
    ++ (encodeUIntLE 4 message.tradeTimeStamp
    ++ (encodeUIntLE 8 message.lastSalePrice
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 4 message.tradeDate))))))))))

def decode (bytes : List UInt8) : Option (TradeCancelledMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (buyBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (sellBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (tradeTimeStamp, bytes) ← decodeUIntLE 4 bytes
  let (lastSalePrice, bytes) ← decodeUIntLE 8 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ symbol, price, volume, buyBrokerNumber, sellBrokerNumber, tradeTimeStamp, lastSalePrice, listingMarket, productType, tradeNumber, tradeDate }, bytes)

@[simp] theorem encode_length (message : TradeCancelledMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, ListingMarket.encode_length, ProductType.encode_length]

theorem encode_length_pos (message : TradeCancelledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCancelledMessage

/-- Moc Imbalance Message: 62 bytes -/
structure MocImbalanceMessage where
  symbol : Alpha 12
  imbalanceSide : ImbalanceSide
  imbalanceVolume : BitVec 32
  tradingSystemTimeStamp : BitVec 64
  imbalanceReferencePrice : BitVec 64
  pairedVolume : BitVec 32
  marketOrderImbalanceVolume : BitVec 32
  marketOrderImbalanceSide : MarketOrderImbalanceSide
  nearIndicativeClosingPrice : BitVec 64
  farIndicativeClosingPrice : BitVec 64
  priceVariation : BitVec 32
  deriving DecidableEq, Repr

namespace MocImbalanceMessage

def encode (message : MocImbalanceMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (ImbalanceSide.encode message.imbalanceSide
    ++ (encodeUIntLE 4 message.imbalanceVolume
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp
    ++ (encodeUIntLE 8 message.imbalanceReferencePrice
    ++ (encodeUIntLE 4 message.pairedVolume
    ++ (encodeUIntLE 4 message.marketOrderImbalanceVolume
    ++ (MarketOrderImbalanceSide.encode message.marketOrderImbalanceSide
    ++ (encodeUIntLE 8 message.nearIndicativeClosingPrice
    ++ (encodeUIntLE 8 message.farIndicativeClosingPrice
    ++ (encodeUIntLE 4 message.priceVariation))))))))))

def decode (bytes : List UInt8) : Option (MocImbalanceMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (imbalanceVolume, bytes) ← decodeUIntLE 4 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (pairedVolume, bytes) ← decodeUIntLE 4 bytes
  let (marketOrderImbalanceVolume, bytes) ← decodeUIntLE 4 bytes
  let (marketOrderImbalanceSide, bytes) ← MarketOrderImbalanceSide.decode bytes
  let (nearIndicativeClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (farIndicativeClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (priceVariation, bytes) ← decodeUIntLE 4 bytes
  pure ({ symbol, imbalanceSide, imbalanceVolume, tradingSystemTimeStamp, imbalanceReferencePrice, pairedVolume, marketOrderImbalanceVolume, marketOrderImbalanceSide, nearIndicativeClosingPrice, farIndicativeClosingPrice, priceVariation }, bytes)

@[simp] theorem encode_length (message : MocImbalanceMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ImbalanceSide.encode_length, encodeUIntLE_length, MarketOrderImbalanceSide.encode_length]

theorem encode_length_pos (message : MocImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MocImbalanceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceSide.decode_encode, some_bind]
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
  rw [List.append_assoc, MarketOrderImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MocImbalanceMessage

/-- Stock Status Message: 84 bytes -/
structure StockStatusMessage where
  symbol : Alpha 12
  comment : Alpha 40
  stockState : Alpha 2
  tradingSystemTimeStamp : BitVec 64
  calculatedClosingPrice : BitVec 64
  vwap : BitVec 64
  resumeTradeTime : BitVec 32
  listingMarket : ListingMarket
  productType : ProductType
  deriving DecidableEq, Repr

namespace StockStatusMessage

def encode (message : StockStatusMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.comment
    ++ (Alpha.encode message.stockState
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp
    ++ (encodeUIntLE 8 message.calculatedClosingPrice
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 4 message.resumeTradeTime
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType))))))))

def decode (bytes : List UInt8) : Option (StockStatusMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (comment, bytes) ← Alpha.decode 40 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  let (calculatedClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (resumeTradeTime, bytes) ← decodeUIntLE 4 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  pure ({ symbol, comment, stockState, tradingSystemTimeStamp, calculatedClosingPrice, vwap, resumeTradeTime, listingMarket, productType }, bytes)

@[simp] theorem encode_length (message : StockStatusMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, ListingMarket.encode_length, ProductType.encode_length]

theorem encode_length_pos (message : StockStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [ProductType.decode_encode, some_bind]
  rfl

end StockStatusMessage

/-- Quote Message: 36 bytes -/
structure QuoteMessage where
  symbol : Alpha 12
  bidPrice : BitVec 64
  bidSize : BitVec 32
  askPrice : BitVec 64
  askSize : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 4 message.bidSize
    ++ (encodeUIntLE 8 message.askPrice
    ++ (encodeUIntLE 4 message.askSize))))

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 8 bytes
  let (askSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ symbol, bidPrice, bidSize, askPrice, askSize }, bytes)

@[simp] theorem encode_length (message : QuoteMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteMessage

/-- Any Business Message, selected by Msg Type -/
inductive BusinessMessage where
  | symbolStatusMessage (message : SymbolStatusMessage) -- "J" 0x4A
  | tradeReportMessage (message : TradeReportMessage) -- "s" 0x73
  | tradeCancelledMessage (message : TradeCancelledMessage) -- "t" 0x74
  | mocImbalanceMessage (message : MocImbalanceMessage) -- "u" 0x75
  | stockStatusMessage (message : StockStatusMessage) -- "v" 0x76
  | quoteMessage (message : QuoteMessage) -- "w" 0x77
  deriving DecidableEq, Repr

namespace BusinessMessage

/-- The Msg Type each message is sent under -/
def tag : BusinessMessage → BitVec 8
  | .symbolStatusMessage _ => 74
  | .tradeReportMessage _ => 115
  | .tradeCancelledMessage _ => 116
  | .mocImbalanceMessage _ => 117
  | .stockStatusMessage _ => 118
  | .quoteMessage _ => 119

def encode : BusinessMessage → List UInt8
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .tradeCancelledMessage message => TradeCancelledMessage.encode message
  | .mocImbalanceMessage message => MocImbalanceMessage.encode message
  | .stockStatusMessage message => StockStatusMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : BusinessMessage) : (encode message).length ≤ 84 := by
  cases message with
  | symbolStatusMessage inner =>
    simp only [encode, SymbolStatusMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | tradeCancelledMessage inner =>
    simp only [encode, TradeCancelledMessage.encode_length]
    omega
  | mocImbalanceMessage inner =>
    simp only [encode, MocImbalanceMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [encode, StockStatusMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [encode, QuoteMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (BusinessMessage × List UInt8) :=
  if tag = 74 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 115 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 116 then (TradeCancelledMessage.decode bytes).map fun (message, rest) => (.tradeCancelledMessage message, rest)
  else if tag = 117 then (MocImbalanceMessage.decode bytes).map fun (message, rest) => (.mocImbalanceMessage message, rest)
  else if tag = 118 then (StockStatusMessage.decode bytes).map fun (message, rest) => (.stockStatusMessage message, rest)
  else if tag = 119 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : BusinessMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end BusinessMessage

/-- Body -/
structure Body where
  businessHeader : BusinessHeader
  businessMessage : BusinessMessage
  deriving DecidableEq, Repr

namespace Body

def encodeBody (message : Body) : List UInt8 :=
  encodeUInt 1 (BusinessMessage.tag message.businessMessage)
    ++ (BusinessHeader.encode message.businessHeader
    ++ (BusinessMessage.encode message.businessMessage))

def decodeBody (bytes : List UInt8) : Option (Body × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (businessHeader, bytes) ← BusinessHeader.decode bytes
  let (businessMessage, bytes) ← BusinessMessage.decode msgType bytes
  pure ({ businessHeader, businessMessage }, bytes)

theorem decodeBody_encodeBody (message : Body) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [BusinessMessage.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Body) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.businessMessage with
  | symbolStatusMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, SymbolStatusMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, TradeReportMessage.encode_length]
    omega
  | tradeCancelledMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, TradeCancelledMessage.encode_length]
    omega
  | mocImbalanceMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, MocImbalanceMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, StockStatusMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, QuoteMessage.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Body → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Body × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Body) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Body) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Body

/-- Packet -/
structure Packet where
  startOfFrame : BitVec 8
  protocolName : ProtocolName
  protocolVersion : Alpha 1
  sessionId : BitVec 32
  ackRequiredPossDup : AckRequiredPossDup
  body : Bounded 1 Body
  deriving DecidableEq, Repr

namespace Packet

def encodeBody (message : Packet) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (AckRequiredPossDup.encode message.ackRequiredPossDup
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.body.val.length)
    ++ (encodeMany Body.encode message.body.val)))

def decodeBody (startOfFrame : BitVec 8) (protocolName : ProtocolName) (protocolVersion : Alpha 1) (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (ackRequiredPossDup, bytes) ← AckRequiredPossDup.decode bytes
  let (numBody, bytes) ← decodeUInt 1 bytes
  let (body_, bytes) ← decodeMany Body.decode numBody.toNat bytes
  if fits_body : body_.length < 256 ^ 1 then
    pure ({ startOfFrame, protocolName, protocolVersion, sessionId, ackRequiredPossDup, body := ⟨body_, fits_body⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : Packet) (rest : List UInt8) :
    decodeBody message.startOfFrame message.protocolName message.protocolVersion (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AckRequiredPossDup.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Body.encode Body.decode Body.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.body.length_lt]
  rfl

/-- Size rule: Message Length counts the bytes after it plus 10, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked; Start Of Frame, Protocol Name, Protocol Version are read ahead of it -/
def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.startOfFrame
    ++ (ProtocolName.encode message.protocolName
    ++ (Alpha.encode message.protocolVersion
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 10)) ++ encodeBody message)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (startOfFrame, bytes) ← decodeUInt 1 bytes
  let (protocolName, bytes) ← ProtocolName.decode bytes
  let (protocolVersion, bytes) ← Alpha.decode 1 bytes
  let (_, bytes) ← decodeUIntLE 2 bytes
  (decodeBody startOfFrame protocolName protocolVersion) bytes

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ProtocolName.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, ProtocolName.encode_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

end Packet

end Omi.TmxTsxQuantumfeedlevel1XmtV26
