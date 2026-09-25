import Omi.Wire

/-!
# Box Options Market Sola Order Entry v2.25

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Number Of Message Types To Be Received counts User Connection Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Note: Number Of Instructions Present In The Message counts Disconnection Instruction Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Note: Number Of Legs counts New Complex Order Instrument Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Note: Nb Legs counts Complex Order Auction Entry Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BoxBoxoptionsSolaorderentrySailV225Firm

/-- Disconnection Instruction Note Cancel Quotes Only Q Quotes Only: one byte code -/
def DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.codes : List UInt8 :=
  [0x41, 0x4C, 0x4F, 0x51]

inductive DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly where
  | all -- All
  | locked -- Locked
  | ordersOnly -- Orders Only
  | quotesOnly -- Quotes Only
  | unlisted (byte : { byte : UInt8 // byte ∉ DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly

def toByte : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly → UInt8
  | .all => 0x41
  | .locked => 0x4C
  | .ordersOnly => 0x4F
  | .quotesOnly => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly :=
  if byte = 0x41 then .all
  else if byte = 0x4C then .locked
  else if byte = 0x4F then .ordersOnly
  else .quotesOnly

def ofByte (byte : UInt8) : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | locked => decide
  | ordersOnly => decide
  | quotesOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly

/-- Active Y On N Off: one byte code -/
def ActiveYOnNOff.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ActiveYOnNOff where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveYOnNOff.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveYOnNOff

def toByte : ActiveYOnNOff → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveYOnNOff :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : ActiveYOnNOff :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveYOnNOff) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActiveYOnNOff) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActiveYOnNOff × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActiveYOnNOff) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ActiveYOnNOff) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActiveYOnNOff

/-- Account Type: one byte code -/
def AccountType.codes : List UInt8 :=
  [0x36, 0x37, 0x38, 0x54, 0x57, 0x58]

inductive AccountType where
  | publicCustomer -- Public Customer
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealerClearedAsCustomer -- Broker Dealer Cleared As Customer
  | awayMarketMaker -- Away Market Maker
  | unlisted (byte : { byte : UInt8 // byte ∉ AccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccountType

def toByte : AccountType → UInt8
  | .publicCustomer => 0x36
  | .brokerDealer => 0x37
  | .marketMaker => 0x38
  | .professionalCustomer => 0x54
  | .brokerDealerClearedAsCustomer => 0x57
  | .awayMarketMaker => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AccountType :=
  if byte = 0x36 then .publicCustomer
  else if byte = 0x37 then .brokerDealer
  else if byte = 0x38 then .marketMaker
  else if byte = 0x54 then .professionalCustomer
  else if byte = 0x57 then .brokerDealerClearedAsCustomer
  else .awayMarketMaker

def ofByte (byte : UInt8) : AccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccountType) : ofByte value.toByte = value := by
  cases value with
  | publicCustomer => decide
  | brokerDealer => decide
  | marketMaker => decide
  | professionalCustomer => decide
  | brokerDealerClearedAsCustomer => decide
  | awayMarketMaker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccountType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccountType

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x43, 0x4F, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x41, 0x42, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50]

inductive OpenClose where
  | closeAllLegsOrSingleInstrument -- Close All Legs Or Single Instrument
  | openAllLegsOrSingleInstrumentForComplexOrdersMustBeUsedItIndicatesThatTheOpenClosePositionsAreSpecifiedInThePostTradingInstructionFieldForLegacySupportTheFollowingValuesAreStillSupportedForComplexOrders -- Open All Legs Or Single Instrument For Complex Orders Must Be Used It Indicates That The Open Close Positions Are Specified In The Post Trading Instruction Field For Legacy Support The Following Values Are Still Supported For Complex Orders
  | legs1StLegOpen2NdLegClose -- Legs 1 St Leg Open 2 Nd Leg Close
  | legs1StLegClose2NdLegOpen -- Legs 1 St Leg Close 2 Nd Leg Open
  | legs1StLegOpen2NdLegOpen3RdLegClose -- Legs 1 St Leg Open 2 Nd Leg Open 3 Rd Leg Close
  | legs1StLegOpen2NdLegClose3RdLegOpen -- Legs 1 St Leg Open 2 Nd Leg Close 3 Rd Leg Open
  | legs1StLegOpen2NdLegClose3RdLegClose -- Legs 1 St Leg Open 2 Nd Leg Close 3 Rd Leg Close
  | legs1StLegClose2NdLegOpen3RdLegOpen -- Legs 1 St Leg Close 2 Nd Leg Open 3 Rd Leg Open
  | legs1StLegClose2NdLegOpen3RdLegClose -- Legs 1 St Leg Close 2 Nd Leg Open 3 Rd Leg Close
  | legs1StLegClose2NdLegClose3RdLegOpen -- Legs 1 St Leg Close 2 Nd Leg Close 3 Rd Leg Open
  | legs1StLegOpen2NdLegOpen3RdLegOpen4ThLegClose -- Legs 1 St Leg Open 2 Nd Leg Open 3 Rd Leg Open 4 Th Leg Close
  | legs1StLegOpen2NdLegOpen3RdLegClose4ThLegOpen -- Legs 1 St Leg Open 2 Nd Leg Open 3 Rd Leg Close 4 Th Leg Open
  | legs1StLegOpen2NdLegOpen3RdLegClose4ThLegClose -- Legs 1 St Leg Open 2 Nd Leg Open 3 Rd Leg Close 4 Th Leg Close
  | legs1StLegOpen2NdLegClose3RdLegOpen4ThLegOpen -- Legs 1 St Leg Open 2 Nd Leg Close 3 Rd Leg Open 4 Th Leg Open
  | legs1StLegOpen2NdLegClose3RdLegOpen4ThLegClose -- Legs 1 St Leg Open 2 Nd Leg Close 3 Rd Leg Open 4 Th Leg Close
  | legs1StLegOpen2NdLegClose3RdLegClose4ThLegOpen -- Legs 1 St Leg Open 2 Nd Leg Close 3 Rd Leg Close 4 Th Leg Open
  | legs1StLegOpen2NdLegClose3RdLegClose4ThLegClose -- Legs 1 St Leg Open 2 Nd Leg Close 3 Rd Leg Close 4 Th Leg Close
  | legs1StLegClose2NdLegOpen3RdLegOpen4ThLegOpen -- Legs 1 St Leg Close 2 Nd Leg Open 3 Rd Leg Open 4 Th Leg Open
  | legs1StLegClose2NdLegOpen3RdLegOpen4ThLegClose -- Legs 1 St Leg Close 2 Nd Leg Open 3 Rd Leg Open 4 Th Leg Close
  | legs1StLegClose2NdLegOpen3RdLegClose4ThLegOpen -- Legs 1 St Leg Close 2 Nd Leg Open 3 Rd Leg Close 4 Th Leg Open
  | legs1StLegClose2NdLegOpen3RdLegClose4ThLegClose -- Legs 1 St Leg Close 2 Nd Leg Open 3 Rd Leg Close 4 Th Leg Close
  | legs1StLegClose2NdLegClose3RdLegOpen4ThLegOpen -- Legs 1 St Leg Close 2 Nd Leg Close 3 Rd Leg Open 4 Th Leg Open
  | legs1StLegClose2NdLegClose3RdLegOpen4ThLegClose -- Legs 1 St Leg Close 2 Nd Leg Close 3 Rd Leg Open 4 Th Leg Close
  | legs1StLegClose2NdLegClose3RdLegClose4ThLegOpen -- Legs 1 St Leg Close 2 Nd Leg Close 3 Rd Leg Close 4 Th Leg Open
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .closeAllLegsOrSingleInstrument => 0x43
  | .openAllLegsOrSingleInstrumentForComplexOrdersMustBeUsedItIndicatesThatTheOpenClosePositionsAreSpecifiedInThePostTradingInstructionFieldForLegacySupportTheFollowingValuesAreStillSupportedForComplexOrders => 0x4F
  | .legs1StLegOpen2NdLegClose => 0x31
  | .legs1StLegClose2NdLegOpen => 0x32
  | .legs1StLegOpen2NdLegOpen3RdLegClose => 0x33
  | .legs1StLegOpen2NdLegClose3RdLegOpen => 0x34
  | .legs1StLegOpen2NdLegClose3RdLegClose => 0x35
  | .legs1StLegClose2NdLegOpen3RdLegOpen => 0x36
  | .legs1StLegClose2NdLegOpen3RdLegClose => 0x37
  | .legs1StLegClose2NdLegClose3RdLegOpen => 0x38
  | .legs1StLegOpen2NdLegOpen3RdLegOpen4ThLegClose => 0x41
  | .legs1StLegOpen2NdLegOpen3RdLegClose4ThLegOpen => 0x42
  | .legs1StLegOpen2NdLegOpen3RdLegClose4ThLegClose => 0x44
  | .legs1StLegOpen2NdLegClose3RdLegOpen4ThLegOpen => 0x45
  | .legs1StLegOpen2NdLegClose3RdLegOpen4ThLegClose => 0x46
  | .legs1StLegOpen2NdLegClose3RdLegClose4ThLegOpen => 0x47
  | .legs1StLegOpen2NdLegClose3RdLegClose4ThLegClose => 0x48
  | .legs1StLegClose2NdLegOpen3RdLegOpen4ThLegOpen => 0x49
  | .legs1StLegClose2NdLegOpen3RdLegOpen4ThLegClose => 0x4A
  | .legs1StLegClose2NdLegOpen3RdLegClose4ThLegOpen => 0x4B
  | .legs1StLegClose2NdLegOpen3RdLegClose4ThLegClose => 0x4C
  | .legs1StLegClose2NdLegClose3RdLegOpen4ThLegOpen => 0x4D
  | .legs1StLegClose2NdLegClose3RdLegOpen4ThLegClose => 0x4E
  | .legs1StLegClose2NdLegClose3RdLegClose4ThLegOpen => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x43 then .closeAllLegsOrSingleInstrument
  else if byte = 0x4F then .openAllLegsOrSingleInstrumentForComplexOrdersMustBeUsedItIndicatesThatTheOpenClosePositionsAreSpecifiedInThePostTradingInstructionFieldForLegacySupportTheFollowingValuesAreStillSupportedForComplexOrders
  else if byte = 0x31 then .legs1StLegOpen2NdLegClose
  else if byte = 0x32 then .legs1StLegClose2NdLegOpen
  else if byte = 0x33 then .legs1StLegOpen2NdLegOpen3RdLegClose
  else if byte = 0x34 then .legs1StLegOpen2NdLegClose3RdLegOpen
  else if byte = 0x35 then .legs1StLegOpen2NdLegClose3RdLegClose
  else if byte = 0x36 then .legs1StLegClose2NdLegOpen3RdLegOpen
  else if byte = 0x37 then .legs1StLegClose2NdLegOpen3RdLegClose
  else if byte = 0x38 then .legs1StLegClose2NdLegClose3RdLegOpen
  else if byte = 0x41 then .legs1StLegOpen2NdLegOpen3RdLegOpen4ThLegClose
  else if byte = 0x42 then .legs1StLegOpen2NdLegOpen3RdLegClose4ThLegOpen
  else if byte = 0x44 then .legs1StLegOpen2NdLegOpen3RdLegClose4ThLegClose
  else if byte = 0x45 then .legs1StLegOpen2NdLegClose3RdLegOpen4ThLegOpen
  else if byte = 0x46 then .legs1StLegOpen2NdLegClose3RdLegOpen4ThLegClose
  else if byte = 0x47 then .legs1StLegOpen2NdLegClose3RdLegClose4ThLegOpen
  else if byte = 0x48 then .legs1StLegOpen2NdLegClose3RdLegClose4ThLegClose
  else if byte = 0x49 then .legs1StLegClose2NdLegOpen3RdLegOpen4ThLegOpen
  else if byte = 0x4A then .legs1StLegClose2NdLegOpen3RdLegOpen4ThLegClose
  else if byte = 0x4B then .legs1StLegClose2NdLegOpen3RdLegClose4ThLegOpen
  else if byte = 0x4C then .legs1StLegClose2NdLegOpen3RdLegClose4ThLegClose
  else if byte = 0x4D then .legs1StLegClose2NdLegClose3RdLegOpen4ThLegOpen
  else if byte = 0x4E then .legs1StLegClose2NdLegClose3RdLegOpen4ThLegClose
  else .legs1StLegClose2NdLegClose3RdLegClose4ThLegOpen

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | closeAllLegsOrSingleInstrument => decide
  | openAllLegsOrSingleInstrumentForComplexOrdersMustBeUsedItIndicatesThatTheOpenClosePositionsAreSpecifiedInThePostTradingInstructionFieldForLegacySupportTheFollowingValuesAreStillSupportedForComplexOrders => decide
  | legs1StLegOpen2NdLegClose => decide
  | legs1StLegClose2NdLegOpen => decide
  | legs1StLegOpen2NdLegOpen3RdLegClose => decide
  | legs1StLegOpen2NdLegClose3RdLegOpen => decide
  | legs1StLegOpen2NdLegClose3RdLegClose => decide
  | legs1StLegClose2NdLegOpen3RdLegOpen => decide
  | legs1StLegClose2NdLegOpen3RdLegClose => decide
  | legs1StLegClose2NdLegClose3RdLegOpen => decide
  | legs1StLegOpen2NdLegOpen3RdLegOpen4ThLegClose => decide
  | legs1StLegOpen2NdLegOpen3RdLegClose4ThLegOpen => decide
  | legs1StLegOpen2NdLegOpen3RdLegClose4ThLegClose => decide
  | legs1StLegOpen2NdLegClose3RdLegOpen4ThLegOpen => decide
  | legs1StLegOpen2NdLegClose3RdLegOpen4ThLegClose => decide
  | legs1StLegOpen2NdLegClose3RdLegClose4ThLegOpen => decide
  | legs1StLegOpen2NdLegClose3RdLegClose4ThLegClose => decide
  | legs1StLegClose2NdLegOpen3RdLegOpen4ThLegOpen => decide
  | legs1StLegClose2NdLegOpen3RdLegOpen4ThLegClose => decide
  | legs1StLegClose2NdLegOpen3RdLegClose4ThLegOpen => decide
  | legs1StLegClose2NdLegOpen3RdLegClose4ThLegClose => decide
  | legs1StLegClose2NdLegClose3RdLegOpen4ThLegOpen => decide
  | legs1StLegClose2NdLegClose3RdLegOpen4ThLegClose => decide
  | legs1StLegClose2NdLegClose3RdLegClose4ThLegOpen => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose

/-- Hedge Spec: one byte code -/
def HedgeSpec.codes : List UInt8 :=
  [0x48, 0x53]

inductive HedgeSpec where
  | hedger -- Hedger
  | speculator -- Speculator
  | unlisted (byte : { byte : UInt8 // byte ∉ HedgeSpec.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HedgeSpec

def toByte : HedgeSpec → UInt8
  | .hedger => 0x48
  | .speculator => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HedgeSpec :=
  if byte = 0x48 then .hedger
  else .speculator

def ofByte (byte : UInt8) : HedgeSpec :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HedgeSpec) : ofByte value.toByte = value := by
  cases value with
  | hedger => decide
  | speculator => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HedgeSpec) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HedgeSpec × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HedgeSpec) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HedgeSpec) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HedgeSpec

/-- Clearing Operation Mode: one byte code -/
def ClearingOperationMode.codes : List UInt8 :=
  [0x43, 0x47, 0x49]

inductive ClearingOperationMode where
  | cmtaClearingMemberTradingAgreementFirmWillBeDefinedInTheClearingDestinationField -- Cmta Clearing Member Trading Agreement Firm Will Be Defined In The Clearing Destination Field
  | giveUpFirmWillBeDefinedInTheClearingDestinationField -- Give Up Firm Will Be Defined In The Clearing Destination Field
  | bothCmtaAndGiveUpFirmsWillBeDefinedInThePostTradingInstructionFieldTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide -- Both Cmta And Give Up Firms Will Be Defined In The Post Trading Instruction Field The Guide States No Width For This Type One Character Is Inferred From The Values It States Each Of Which Is One Character Wide
  | unlisted (byte : { byte : UInt8 // byte ∉ ClearingOperationMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClearingOperationMode

def toByte : ClearingOperationMode → UInt8
  | .cmtaClearingMemberTradingAgreementFirmWillBeDefinedInTheClearingDestinationField => 0x43
  | .giveUpFirmWillBeDefinedInTheClearingDestinationField => 0x47
  | .bothCmtaAndGiveUpFirmsWillBeDefinedInThePostTradingInstructionFieldTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClearingOperationMode :=
  if byte = 0x43 then .cmtaClearingMemberTradingAgreementFirmWillBeDefinedInTheClearingDestinationField
  else if byte = 0x47 then .giveUpFirmWillBeDefinedInTheClearingDestinationField
  else .bothCmtaAndGiveUpFirmsWillBeDefinedInThePostTradingInstructionFieldTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide

def ofByte (byte : UInt8) : ClearingOperationMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClearingOperationMode) : ofByte value.toByte = value := by
  cases value with
  | cmtaClearingMemberTradingAgreementFirmWillBeDefinedInTheClearingDestinationField => decide
  | giveUpFirmWillBeDefinedInTheClearingDestinationField => decide
  | bothCmtaAndGiveUpFirmsWillBeDefinedInThePostTradingInstructionFieldTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClearingOperationMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClearingOperationMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClearingOperationMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClearingOperationMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClearingOperationMode

/-- Type Of Cancellation Q Quotes Only: one byte code -/
def TypeOfCancellationQQuotesOnly.codes : List UInt8 :=
  [0x41, 0x4C, 0x4F, 0x51]

inductive TypeOfCancellationQQuotesOnly where
  | all -- All
  | locked -- Locked
  | ordersOnly -- Orders Only
  | quotesOnly -- Quotes Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfCancellationQQuotesOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfCancellationQQuotesOnly

def toByte : TypeOfCancellationQQuotesOnly → UInt8
  | .all => 0x41
  | .locked => 0x4C
  | .ordersOnly => 0x4F
  | .quotesOnly => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfCancellationQQuotesOnly :=
  if byte = 0x41 then .all
  else if byte = 0x4C then .locked
  else if byte = 0x4F then .ordersOnly
  else .quotesOnly

def ofByte (byte : UInt8) : TypeOfCancellationQQuotesOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfCancellationQQuotesOnly) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | locked => decide
  | ordersOnly => decide
  | quotesOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfCancellationQQuotesOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfCancellationQQuotesOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfCancellationQQuotesOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfCancellationQQuotesOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfCancellationQQuotesOnly

/-- Type Of Cancellation: one byte code -/
def TypeOfCancellation.codes : List UInt8 :=
  [0x41, 0x4C, 0x4F, 0x51]

inductive TypeOfCancellation where
  | all -- All
  | locked -- Locked
  | ordersOnly -- Orders Only
  | quotesOnly -- Quotes Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfCancellation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfCancellation

def toByte : TypeOfCancellation → UInt8
  | .all => 0x41
  | .locked => 0x4C
  | .ordersOnly => 0x4F
  | .quotesOnly => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfCancellation :=
  if byte = 0x41 then .all
  else if byte = 0x4C then .locked
  else if byte = 0x4F then .ordersOnly
  else .quotesOnly

def ofByte (byte : UInt8) : TypeOfCancellation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfCancellation) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | locked => decide
  | ordersOnly => decide
  | quotesOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfCancellation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfCancellation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfCancellation) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfCancellation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfCancellation

/-- Verb Side: one byte code -/
def VerbSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive VerbSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ VerbSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace VerbSide

def toByte : VerbSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : VerbSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : VerbSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : VerbSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : VerbSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (VerbSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : VerbSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : VerbSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end VerbSide

/-- Special Price Term: one byte code -/
def SpecialPriceTerm.codes : List UInt8 :=
  [0x42, 0x43, 0x47, 0x58, 0x4F, 0x50, 0x52, 0x41]

inductive SpecialPriceTerm where
  | solicitationAuction -- Solicitation Auction
  | facilitationAuction -- Facilitation Auction
  | regularPip -- Regular Pip
  | customerCrossOrderOrQualifiedContingentCrossOrder -- Customer Cross Order Or Qualified Contingent Cross Order
  | directedOrder -- Directed Order
  | preferencedOrder -- Preferenced Order
  | floorTrade -- Floor Trade
  | indicationOfInterest -- Indication Of Interest
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialPriceTerm.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialPriceTerm

def toByte : SpecialPriceTerm → UInt8
  | .solicitationAuction => 0x42
  | .facilitationAuction => 0x43
  | .regularPip => 0x47
  | .customerCrossOrderOrQualifiedContingentCrossOrder => 0x58
  | .directedOrder => 0x4F
  | .preferencedOrder => 0x50
  | .floorTrade => 0x52
  | .indicationOfInterest => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialPriceTerm :=
  if byte = 0x42 then .solicitationAuction
  else if byte = 0x43 then .facilitationAuction
  else if byte = 0x47 then .regularPip
  else if byte = 0x58 then .customerCrossOrderOrQualifiedContingentCrossOrder
  else if byte = 0x4F then .directedOrder
  else if byte = 0x50 then .preferencedOrder
  else if byte = 0x52 then .floorTrade
  else .indicationOfInterest

def ofByte (byte : UInt8) : SpecialPriceTerm :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialPriceTerm) : ofByte value.toByte = value := by
  cases value with
  | solicitationAuction => decide
  | facilitationAuction => decide
  | regularPip => decide
  | customerCrossOrderOrQualifiedContingentCrossOrder => decide
  | directedOrder => decide
  | preferencedOrder => decide
  | floorTrade => decide
  | indicationOfInterest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialPriceTerm) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialPriceTerm × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialPriceTerm) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SpecialPriceTerm) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialPriceTerm

/-- Quantity Term Quantity Term 1: one byte code -/
def QuantityTermQuantityTerm1.codes : List UInt8 :=
  [0x42, 0x4A]

inductive QuantityTermQuantityTerm1 where
  | surrenderQuantityForSolicitationFacilitationAndFloorTrade -- Surrender Quantity For Solicitation Facilitation And Floor Trade
  | indicatesThatTheAuctionTypeAsMip -- Indicates That The Auction Type As Mip
  | unlisted (byte : { byte : UInt8 // byte ∉ QuantityTermQuantityTerm1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuantityTermQuantityTerm1

def toByte : QuantityTermQuantityTerm1 → UInt8
  | .surrenderQuantityForSolicitationFacilitationAndFloorTrade => 0x42
  | .indicatesThatTheAuctionTypeAsMip => 0x4A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuantityTermQuantityTerm1 :=
  if byte = 0x42 then .surrenderQuantityForSolicitationFacilitationAndFloorTrade
  else .indicatesThatTheAuctionTypeAsMip

def ofByte (byte : UInt8) : QuantityTermQuantityTerm1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuantityTermQuantityTerm1) : ofByte value.toByte = value := by
  cases value with
  | surrenderQuantityForSolicitationFacilitationAndFloorTrade => decide
  | indicatesThatTheAuctionTypeAsMip => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuantityTermQuantityTerm1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuantityTermQuantityTerm1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuantityTermQuantityTerm1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuantityTermQuantityTerm1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuantityTermQuantityTerm1

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x4C, 0x4F, 0x57]

inductive PriceType where
  | limitPriceSetInMessage -- Limit Price Set In Message
  | atOpeningPrice -- At Opening Price
  | atAnyPriceMarketOrder -- At Any Price Market Order
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .limitPriceSetInMessage => 0x4C
  | .atOpeningPrice => 0x4F
  | .atAnyPriceMarketOrder => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x4C then .limitPriceSetInMessage
  else if byte = 0x4F then .atOpeningPrice
  else .atAnyPriceMarketOrder

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | limitPriceSetInMessage => decide
  | atOpeningPrice => decide
  | atAnyPriceMarketOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceType

/-- Duration Type: one byte code -/
def DurationType.codes : List UInt8 :=
  [0x41, 0x44, 0x45, 0x46, 0x4A, 0x57]

inductive DurationType where
  | auctionOrKill -- Auction Or Kill
  | orderIsValidUntilGtdDateGtd -- Order Is Valid Until Gtd Date Gtd
  | immediateOrderCannotBeBookedFak -- Immediate Order Cannot Be Booked Fak
  | validUntilInstrumentExpirationGtc -- Valid Until Instrument Expiration Gtc
  | validForTheCurrentDayOnlyDay -- Valid For The Current Day Only Day
  | validForTheCurrentSessionOrderOnly -- Valid For The Current Session Order Only
  | unlisted (byte : { byte : UInt8 // byte ∉ DurationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DurationType

def toByte : DurationType → UInt8
  | .auctionOrKill => 0x41
  | .orderIsValidUntilGtdDateGtd => 0x44
  | .immediateOrderCannotBeBookedFak => 0x45
  | .validUntilInstrumentExpirationGtc => 0x46
  | .validForTheCurrentDayOnlyDay => 0x4A
  | .validForTheCurrentSessionOrderOnly => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DurationType :=
  if byte = 0x41 then .auctionOrKill
  else if byte = 0x44 then .orderIsValidUntilGtdDateGtd
  else if byte = 0x45 then .immediateOrderCannotBeBookedFak
  else if byte = 0x46 then .validUntilInstrumentExpirationGtc
  else if byte = 0x4A then .validForTheCurrentDayOnlyDay
  else .validForTheCurrentSessionOrderOnly

def ofByte (byte : UInt8) : DurationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DurationType) : ofByte value.toByte = value := by
  cases value with
  | auctionOrKill => decide
  | orderIsValidUntilGtdDateGtd => decide
  | immediateOrderCannotBeBookedFak => decide
  | validUntilInstrumentExpirationGtc => decide
  | validForTheCurrentDayOnlyDay => decide
  | validForTheCurrentSessionOrderOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DurationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DurationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DurationType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DurationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DurationType

/-- Enabled Y Yes N No: one byte code -/
def EnabledYYesNNo.codes : List UInt8 :=
  [0x59, 0x4E]

inductive EnabledYYesNNo where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ EnabledYYesNNo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EnabledYYesNNo

def toByte : EnabledYYesNNo → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EnabledYYesNNo :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : EnabledYYesNNo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EnabledYYesNNo) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EnabledYYesNNo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EnabledYYesNNo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EnabledYYesNNo) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EnabledYYesNNo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EnabledYYesNNo

/-- Leg Verb: one byte code -/
def LegVerb.codes : List UInt8 :=
  [0x42, 0x53]

inductive LegVerb where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegVerb

def toByte : LegVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegVerb :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : LegVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegVerb) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegVerb

/-- Protection Type Advanced Normal: one byte code -/
def ProtectionTypeAdvancedNormal.codes : List UInt8 :=
  [0x41, 0x43, 0x4E]

inductive ProtectionTypeAdvancedNormal where
  | advancedProtection -- Advanced Protection
  | functionallyEquivalentToN -- Functionally Equivalent To N
  | standardProtection -- Standard Protection
  | unlisted (byte : { byte : UInt8 // byte ∉ ProtectionTypeAdvancedNormal.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProtectionTypeAdvancedNormal

def toByte : ProtectionTypeAdvancedNormal → UInt8
  | .advancedProtection => 0x41
  | .functionallyEquivalentToN => 0x43
  | .standardProtection => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProtectionTypeAdvancedNormal :=
  if byte = 0x41 then .advancedProtection
  else if byte = 0x43 then .functionallyEquivalentToN
  else .standardProtection

def ofByte (byte : UInt8) : ProtectionTypeAdvancedNormal :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProtectionTypeAdvancedNormal) : ofByte value.toByte = value := by
  cases value with
  | advancedProtection => decide
  | functionallyEquivalentToN => decide
  | standardProtection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProtectionTypeAdvancedNormal) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProtectionTypeAdvancedNormal × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProtectionTypeAdvancedNormal) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ProtectionTypeAdvancedNormal) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProtectionTypeAdvancedNormal

/-- User Connection Occurrence: 2 bytes -/
structure UserConnectionOccurrence where
  messageTypesToBeReceived : Alpha 2
  deriving DecidableEq, Repr

namespace UserConnectionOccurrence

def encode (message : UserConnectionOccurrence) : List UInt8 :=
  Alpha.encode message.messageTypesToBeReceived

def decode (bytes : List UInt8) : Option (UserConnectionOccurrence × List UInt8) := do
  let (messageTypesToBeReceived, bytes) ← Alpha.decode 2 bytes
  pure ({ messageTypesToBeReceived }, bytes)

@[simp] theorem encode_length (message : UserConnectionOccurrence) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UserConnectionOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserConnectionOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserConnectionOccurrence

/-- User Connection -/
structure UserConnection where
  protocolVersion : Alpha 2
  userId : Alpha 8
  passwordMd5Encryption : Alpha 8
  sessionId : Alpha 4
  timeHhmmss : Alpha 6
  exchangeMessageId : Alpha 6
  inactivityInterval : Alpha 2
  userConnectionOccurrence : Digited 2 UserConnectionOccurrence
  deriving DecidableEq, Repr

namespace UserConnection

def encode (message : UserConnection) : List UInt8 :=
  Alpha.encode message.protocolVersion
    ++ (Alpha.encode message.userId
    ++ (Alpha.encode message.passwordMd5Encryption
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.timeHhmmss
    ++ (Alpha.encode message.exchangeMessageId
    ++ (Alpha.encode message.inactivityInterval
    ++ (encodeDigits 2 message.userConnectionOccurrence.val.length
    ++ (encodeMany UserConnectionOccurrence.encode message.userConnectionOccurrence.val))))))))

def decode (bytes : List UInt8) : Option (UserConnection × List UInt8) := do
  let (protocolVersion, bytes) ← Alpha.decode 2 bytes
  let (userId, bytes) ← Alpha.decode 8 bytes
  let (passwordMd5Encryption, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← Alpha.decode 4 bytes
  let (timeHhmmss, bytes) ← Alpha.decode 6 bytes
  let (exchangeMessageId, bytes) ← Alpha.decode 6 bytes
  let (inactivityInterval, bytes) ← Alpha.decode 2 bytes
  let (numberOfMessageTypesToBeReceived, bytes) ← decodeDigits 2 bytes
  let (userConnectionOccurrence_, bytes) ← decodeMany UserConnectionOccurrence.decode numberOfMessageTypesToBeReceived bytes
  if fits_userConnectionOccurrence : userConnectionOccurrence_.length < 10 ^ 2 then
    pure ({ protocolVersion, userId, passwordMd5Encryption, sessionId, timeHhmmss, exchangeMessageId, inactivityInterval, userConnectionOccurrence := ⟨userConnectionOccurrence_, fits_userConnectionOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : UserConnection) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UserConnection) : (encode message).length ≤ 236 := by
  have bound_userConnectionOccurrence := message.userConnectionOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const UserConnectionOccurrence.encode 2 UserConnectionOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : UserConnection) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.userConnectionOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany UserConnectionOccurrence.encode UserConnectionOccurrence.decode UserConnectionOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.userConnectionOccurrence.length_lt]
  rfl

end UserConnection

/-- User Disconnection: 12 bytes -/
structure UserDisconnection where
  userId : Alpha 8
  sessionId : Alpha 4
  deriving DecidableEq, Repr

namespace UserDisconnection

def encode (message : UserDisconnection) : List UInt8 :=
  Alpha.encode message.userId
    ++ (Alpha.encode message.sessionId)

def decode (bytes : List UInt8) : Option (UserDisconnection × List UInt8) := do
  let (userId, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← Alpha.decode 4 bytes
  pure ({ userId, sessionId }, bytes)

@[simp] theorem encode_length (message : UserDisconnection) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UserDisconnection) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserDisconnection) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserDisconnection

/-- Disconnection Instruction Occurrence: 10 bytes -/
structure DisconnectionInstructionOccurrence where
  traderId : Alpha 8
  disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly
  activeYOnNOff : ActiveYOnNOff
  deriving DecidableEq, Repr

namespace DisconnectionInstructionOccurrence

def encode (message : DisconnectionInstructionOccurrence) : List UInt8 :=
  Alpha.encode message.traderId
    ++ (DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.encode message.disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly
    ++ (ActiveYOnNOff.encode message.activeYOnNOff))

def decode (bytes : List UInt8) : Option (DisconnectionInstructionOccurrence × List UInt8) := do
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly, bytes) ← DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.decode bytes
  let (activeYOnNOff, bytes) ← ActiveYOnNOff.decode bytes
  pure ({ traderId, disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly, activeYOnNOff }, bytes)

@[simp] theorem encode_length (message : DisconnectionInstructionOccurrence) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.encode_length, ActiveYOnNOff.encode_length]

theorem encode_length_pos (message : DisconnectionInstructionOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionInstructionOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.decode_encode, some_bind]
  dsimp only
  rw [ActiveYOnNOff.decode_encode, some_bind]
  rfl

end DisconnectionInstructionOccurrence

/-- Disconnection Instruction -/
structure DisconnectionInstruction where
  disconnectionInstructionOccurrence : Digited 2 DisconnectionInstructionOccurrence
  deriving DecidableEq, Repr

namespace DisconnectionInstruction

def encode (message : DisconnectionInstruction) : List UInt8 :=
  encodeDigits 2 message.disconnectionInstructionOccurrence.val.length
    ++ (encodeMany DisconnectionInstructionOccurrence.encode message.disconnectionInstructionOccurrence.val)

def decode (bytes : List UInt8) : Option (DisconnectionInstruction × List UInt8) := do
  let (numberOfInstructionsPresentInTheMessage, bytes) ← decodeDigits 2 bytes
  let (disconnectionInstructionOccurrence_, bytes) ← decodeMany DisconnectionInstructionOccurrence.decode numberOfInstructionsPresentInTheMessage bytes
  if fits_disconnectionInstructionOccurrence : disconnectionInstructionOccurrence_.length < 10 ^ 2 then
    pure ({ disconnectionInstructionOccurrence := ⟨disconnectionInstructionOccurrence_, fits_disconnectionInstructionOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : DisconnectionInstruction) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeDigits_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DisconnectionInstruction) : (encode message).length ≤ 992 := by
  have bound_disconnectionInstructionOccurrence := message.disconnectionInstructionOccurrence.length_lt
  unfold encode
  simp only [List.length_append, encodeDigits_length, encodeMany_length_const DisconnectionInstructionOccurrence.encode 10 DisconnectionInstructionOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : DisconnectionInstruction) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.disconnectionInstructionOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany DisconnectionInstructionOccurrence.encode DisconnectionInstructionOccurrence.decode DisconnectionInstructionOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.disconnectionInstructionOccurrence.length_lt]
  rfl

end DisconnectionInstruction

/-- Heartbeat Response: 20 bytes -/
structure HeartbeatResponse where
  userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod : Alpha 8
  lastExchangeMessageIdSentToParticipant : Alpha 6
  timeLocal : Alpha 6
  deriving DecidableEq, Repr

namespace HeartbeatResponse

def encode (message : HeartbeatResponse) : List UInt8 :=
  Alpha.encode message.userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod
    ++ (Alpha.encode message.lastExchangeMessageIdSentToParticipant
    ++ (Alpha.encode message.timeLocal))

def decode (bytes : List UInt8) : Option (HeartbeatResponse × List UInt8) := do
  let (userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, bytes) ← Alpha.decode 8 bytes
  let (lastExchangeMessageIdSentToParticipant, bytes) ← Alpha.decode 6 bytes
  let (timeLocal, bytes) ← Alpha.decode 6 bytes
  pure ({ userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, lastExchangeMessageIdSentToParticipant, timeLocal }, bytes)

@[simp] theorem encode_length (message : HeartbeatResponse) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatResponse

/-- Clearing Data: 20 bytes -/
structure ClearingData where
  clearingInstruction : Alpha 12
  accountType : AccountType
  openClose : OpenClose
  hedgeSpec : HedgeSpec
  clearingOperationMode : ClearingOperationMode
  clearingDestination : Alpha 4
  deriving DecidableEq, Repr

namespace ClearingData

def encode (message : ClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (HedgeSpec.encode message.hedgeSpec
    ++ (ClearingOperationMode.encode message.clearingOperationMode
    ++ (Alpha.encode message.clearingDestination)))))

def decode (bytes : List UInt8) : Option (ClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (hedgeSpec, bytes) ← HedgeSpec.decode bytes
  let (clearingOperationMode, bytes) ← ClearingOperationMode.decode bytes
  let (clearingDestination, bytes) ← Alpha.decode 4 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, clearingOperationMode, clearingDestination }, bytes)

@[simp] theorem encode_length (message : ClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length, HedgeSpec.encode_length, ClearingOperationMode.encode_length]

theorem encode_length_pos (message : ClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HedgeSpec.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingOperationMode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingData

/-- Owner Data: 71 bytes -/
structure OwnerData where
  clientOrderId : Alpha 20
  poundSign : Alpha 1
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace OwnerData

def encode (message : OwnerData) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.poundSign
    ++ (Alpha.encode message.memo))

def decode (bytes : List UInt8) : Option (OwnerData × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (poundSign, bytes) ← Alpha.decode 1 bytes
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ clientOrderId, poundSign, memo }, bytes)

@[simp] theorem encode_length (message : OwnerData) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OwnerData

/-- Bulk Quote Data: 203 bytes -/
structure BulkQuoteData where
  group : Alpha 2
  clearingData : ClearingData
  ownerData : OwnerData
  fillerMustBeBlankString22 : Alpha 2
  fillerMustBeBlank2String88 : Alpha 8
  fillerMustBeBlank3String22 : Alpha 2
  calculationTimeInterval : Alpha 8
  maximumTotalVolume : Alpha 8
  maximumTotalValue : Alpha 8
  maximumDeltaVolume : Alpha 8
  maximumDeltaValue : Alpha 8
  percentOfQuote : Alpha 8
  postTradingInstructions : Alpha 50
  deriving DecidableEq, Repr

namespace BulkQuoteData

def encode (message : BulkQuoteData) : List UInt8 :=
  Alpha.encode message.group
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.fillerMustBeBlankString22
    ++ (Alpha.encode message.fillerMustBeBlank2String88
    ++ (Alpha.encode message.fillerMustBeBlank3String22
    ++ (Alpha.encode message.calculationTimeInterval
    ++ (Alpha.encode message.maximumTotalVolume
    ++ (Alpha.encode message.maximumTotalValue
    ++ (Alpha.encode message.maximumDeltaVolume
    ++ (Alpha.encode message.maximumDeltaValue
    ++ (Alpha.encode message.percentOfQuote
    ++ (Alpha.encode message.postTradingInstructions))))))))))))

def decode (bytes : List UInt8) : Option (BulkQuoteData × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (fillerMustBeBlankString22, bytes) ← Alpha.decode 2 bytes
  let (fillerMustBeBlank2String88, bytes) ← Alpha.decode 8 bytes
  let (fillerMustBeBlank3String22, bytes) ← Alpha.decode 2 bytes
  let (calculationTimeInterval, bytes) ← Alpha.decode 8 bytes
  let (maximumTotalVolume, bytes) ← Alpha.decode 8 bytes
  let (maximumTotalValue, bytes) ← Alpha.decode 8 bytes
  let (maximumDeltaVolume, bytes) ← Alpha.decode 8 bytes
  let (maximumDeltaValue, bytes) ← Alpha.decode 8 bytes
  let (percentOfQuote, bytes) ← Alpha.decode 8 bytes
  let (postTradingInstructions, bytes) ← Alpha.decode 50 bytes
  pure ({ group, clearingData, ownerData, fillerMustBeBlankString22, fillerMustBeBlank2String88, fillerMustBeBlank3String22, calculationTimeInterval, maximumTotalVolume, maximumTotalValue, maximumDeltaVolume, maximumDeltaValue, percentOfQuote, postTradingInstructions }, bytes)

@[simp] theorem encode_length (message : BulkQuoteData) : (encode message).length = 203 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : BulkQuoteData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
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

end BulkQuoteData

/-- Global Cancellation: 11 bytes -/
structure GlobalCancellation where
  group : Alpha 2
  typeOfCancellationQQuotesOnly : TypeOfCancellationQQuotesOnly
  mmCatUserTime : Alpha 8
  deriving DecidableEq, Repr

namespace GlobalCancellation

def encode (message : GlobalCancellation) : List UInt8 :=
  Alpha.encode message.group
    ++ (TypeOfCancellationQQuotesOnly.encode message.typeOfCancellationQQuotesOnly
    ++ (Alpha.encode message.mmCatUserTime))

def decode (bytes : List UInt8) : Option (GlobalCancellation × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (typeOfCancellationQQuotesOnly, bytes) ← TypeOfCancellationQQuotesOnly.decode bytes
  let (mmCatUserTime, bytes) ← Alpha.decode 8 bytes
  pure ({ group, typeOfCancellationQQuotesOnly, mmCatUserTime }, bytes)

@[simp] theorem encode_length (message : GlobalCancellation) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TypeOfCancellationQQuotesOnly.encode_length]

theorem encode_length_pos (message : GlobalCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlobalCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfCancellationQQuotesOnly.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GlobalCancellation

/-- User Global Cancellation: 23 bytes -/
structure UserGlobalCancellation where
  group : Alpha 2
  instrument : Alpha 4
  typeOfCancellation : TypeOfCancellation
  accountTypeFilter : Alpha 8
  mmCatUserTime : Alpha 8
  deriving DecidableEq, Repr

namespace UserGlobalCancellation

def encode (message : UserGlobalCancellation) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (TypeOfCancellation.encode message.typeOfCancellation
    ++ (Alpha.encode message.accountTypeFilter
    ++ (Alpha.encode message.mmCatUserTime))))

def decode (bytes : List UInt8) : Option (UserGlobalCancellation × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (typeOfCancellation, bytes) ← TypeOfCancellation.decode bytes
  let (accountTypeFilter, bytes) ← Alpha.decode 8 bytes
  let (mmCatUserTime, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, typeOfCancellation, accountTypeFilter, mmCatUserTime }, bytes)

@[simp] theorem encode_length (message : UserGlobalCancellation) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TypeOfCancellation.encode_length]

theorem encode_length_pos (message : UserGlobalCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserGlobalCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfCancellation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserGlobalCancellation

/-- Directed Routed Order Rejection And Quote: 44 bytes -/
structure DirectedRoutedOrderRejectionAndQuote where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderIdOrderId8 : Alpha 8
  rejectionCode : Alpha 4
  quoteQuantity : Alpha 8
  quotePrice : Alpha 10
  deriving DecidableEq, Repr

namespace DirectedRoutedOrderRejectionAndQuote

def encode (message : DirectedRoutedOrderRejectionAndQuote) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderIdOrderId8
    ++ (Alpha.encode message.rejectionCode
    ++ (Alpha.encode message.quoteQuantity
    ++ (Alpha.encode message.quotePrice))))))

def decode (bytes : List UInt8) : Option (DirectedRoutedOrderRejectionAndQuote × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (rejectionCode, bytes) ← Alpha.decode 4 bytes
  let (quoteQuantity, bytes) ← Alpha.decode 8 bytes
  let (quotePrice, bytes) ← Alpha.decode 10 bytes
  pure ({ group, instrument, traderId, orderIdOrderId8, rejectionCode, quoteQuantity, quotePrice }, bytes)

@[simp] theorem encode_length (message : DirectedRoutedOrderRejectionAndQuote) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DirectedRoutedOrderRejectionAndQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DirectedRoutedOrderRejectionAndQuote) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DirectedRoutedOrderRejectionAndQuote

/-- Buying Clearing Data: 20 bytes -/
structure BuyingClearingData where
  clearingInstruction : Alpha 12
  accountType : AccountType
  openClose : OpenClose
  hedgeSpec : HedgeSpec
  clearingOperationMode : ClearingOperationMode
  clearingDestination : Alpha 4
  deriving DecidableEq, Repr

namespace BuyingClearingData

def encode (message : BuyingClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (HedgeSpec.encode message.hedgeSpec
    ++ (ClearingOperationMode.encode message.clearingOperationMode
    ++ (Alpha.encode message.clearingDestination)))))

def decode (bytes : List UInt8) : Option (BuyingClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (hedgeSpec, bytes) ← HedgeSpec.decode bytes
  let (clearingOperationMode, bytes) ← ClearingOperationMode.decode bytes
  let (clearingDestination, bytes) ← Alpha.decode 4 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, clearingOperationMode, clearingDestination }, bytes)

@[simp] theorem encode_length (message : BuyingClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length, HedgeSpec.encode_length, ClearingOperationMode.encode_length]

theorem encode_length_pos (message : BuyingClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BuyingClearingData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HedgeSpec.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingOperationMode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BuyingClearingData

/-- Selling Clearing Data: 20 bytes -/
structure SellingClearingData where
  clearingInstruction : Alpha 12
  accountType : AccountType
  openClose : OpenClose
  hedgeSpec : HedgeSpec
  clearingOperationMode : ClearingOperationMode
  clearingDestination : Alpha 4
  deriving DecidableEq, Repr

namespace SellingClearingData

def encode (message : SellingClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (HedgeSpec.encode message.hedgeSpec
    ++ (ClearingOperationMode.encode message.clearingOperationMode
    ++ (Alpha.encode message.clearingDestination)))))

def decode (bytes : List UInt8) : Option (SellingClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (hedgeSpec, bytes) ← HedgeSpec.decode bytes
  let (clearingOperationMode, bytes) ← ClearingOperationMode.decode bytes
  let (clearingDestination, bytes) ← Alpha.decode 4 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, clearingOperationMode, clearingDestination }, bytes)

@[simp] theorem encode_length (message : SellingClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length, HedgeSpec.encode_length, ClearingOperationMode.encode_length]

theorem encode_length_pos (message : SellingClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SellingClearingData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HedgeSpec.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingOperationMode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SellingClearingData

/-- Buying Owner Data: 71 bytes -/
structure BuyingOwnerData where
  clientOrderId : Alpha 20
  poundSign : Alpha 1
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace BuyingOwnerData

def encode (message : BuyingOwnerData) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.poundSign
    ++ (Alpha.encode message.memo))

def decode (bytes : List UInt8) : Option (BuyingOwnerData × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (poundSign, bytes) ← Alpha.decode 1 bytes
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ clientOrderId, poundSign, memo }, bytes)

@[simp] theorem encode_length (message : BuyingOwnerData) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BuyingOwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BuyingOwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BuyingOwnerData

/-- Selling Owner Data: 71 bytes -/
structure SellingOwnerData where
  clientOrderId : Alpha 20
  poundSign : Alpha 1
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace SellingOwnerData

def encode (message : SellingOwnerData) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.poundSign
    ++ (Alpha.encode message.memo))

def decode (bytes : List UInt8) : Option (SellingOwnerData × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (poundSign, bytes) ← Alpha.decode 1 bytes
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ clientOrderId, poundSign, memo }, bytes)

@[simp] theorem encode_length (message : SellingOwnerData) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SellingOwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SellingOwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SellingOwnerData

/-- Auction Entry: 364 bytes -/
structure AuctionEntry where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantity : Alpha 8
  price : Alpha 10
  buyingClearingData : BuyingClearingData
  sellingClearingData : SellingClearingData
  buyingOwnerData : BuyingOwnerData
  sellingOwnerData : SellingOwnerData
  imlHandling : Alpha 1
  specialPriceTerm : SpecialPriceTerm
  additionalPrice : Alpha 10
  quantityTermQuantityTerm1 : QuantityTermQuantityTerm1
  additionalQuantityAdditionalQuantity8 : Alpha 8
  buyingPostTradingInstruction : Alpha 50
  sellingPostTradingInstruction : Alpha 50
  buyingAdditionalClientMemo : Alpha 16
  sellingAdditionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  deriving DecidableEq, Repr

namespace AuctionEntry

def encode (message : AuctionEntry) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (BuyingClearingData.encode message.buyingClearingData
    ++ (SellingClearingData.encode message.sellingClearingData
    ++ (BuyingOwnerData.encode message.buyingOwnerData
    ++ (SellingOwnerData.encode message.sellingOwnerData
    ++ (Alpha.encode message.imlHandling
    ++ (SpecialPriceTerm.encode message.specialPriceTerm
    ++ (Alpha.encode message.additionalPrice
    ++ (QuantityTermQuantityTerm1.encode message.quantityTermQuantityTerm1
    ++ (Alpha.encode message.additionalQuantityAdditionalQuantity8
    ++ (Alpha.encode message.buyingPostTradingInstruction
    ++ (Alpha.encode message.sellingPostTradingInstruction
    ++ (Alpha.encode message.buyingAdditionalClientMemo
    ++ (Alpha.encode message.sellingAdditionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44))))))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionEntry × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (buyingClearingData, bytes) ← BuyingClearingData.decode bytes
  let (sellingClearingData, bytes) ← SellingClearingData.decode bytes
  let (buyingOwnerData, bytes) ← BuyingOwnerData.decode bytes
  let (sellingOwnerData, bytes) ← SellingOwnerData.decode bytes
  let (imlHandling, bytes) ← Alpha.decode 1 bytes
  let (specialPriceTerm, bytes) ← SpecialPriceTerm.decode bytes
  let (additionalPrice, bytes) ← Alpha.decode 10 bytes
  let (quantityTermQuantityTerm1, bytes) ← QuantityTermQuantityTerm1.decode bytes
  let (additionalQuantityAdditionalQuantity8, bytes) ← Alpha.decode 8 bytes
  let (buyingPostTradingInstruction, bytes) ← Alpha.decode 50 bytes
  let (sellingPostTradingInstruction, bytes) ← Alpha.decode 50 bytes
  let (buyingAdditionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (sellingAdditionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, verbSide, quantity, price, buyingClearingData, sellingClearingData, buyingOwnerData, sellingOwnerData, imlHandling, specialPriceTerm, additionalPrice, quantityTermQuantityTerm1, additionalQuantityAdditionalQuantity8, buyingPostTradingInstruction, sellingPostTradingInstruction, buyingAdditionalClientMemo, sellingAdditionalClientMemo, fillerMustBeBlankString44 }, bytes)

@[simp] theorem encode_length (message : AuctionEntry) : (encode message).length = 364 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, BuyingClearingData.encode_length, SellingClearingData.encode_length, BuyingOwnerData.encode_length, SellingOwnerData.encode_length, SpecialPriceTerm.encode_length, QuantityTermQuantityTerm1.encode_length]

theorem encode_length_pos (message : AuctionEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyingClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellingClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyingOwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellingOwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialPriceTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantityTermQuantityTerm1.decode_encode, some_bind]
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

end AuctionEntry

/-- Clearing Data Dealer: 20 bytes -/
structure ClearingDataDealer where
  clearingInstruction : Alpha 12
  accountType : AccountType
  openClose : OpenClose
  hedgeSpec : HedgeSpec
  clearingOperationMode : ClearingOperationMode
  clearingDestination : Alpha 4
  deriving DecidableEq, Repr

namespace ClearingDataDealer

def encode (message : ClearingDataDealer) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (HedgeSpec.encode message.hedgeSpec
    ++ (ClearingOperationMode.encode message.clearingOperationMode
    ++ (Alpha.encode message.clearingDestination)))))

def decode (bytes : List UInt8) : Option (ClearingDataDealer × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (hedgeSpec, bytes) ← HedgeSpec.decode bytes
  let (clearingOperationMode, bytes) ← ClearingOperationMode.decode bytes
  let (clearingDestination, bytes) ← Alpha.decode 4 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, clearingOperationMode, clearingDestination }, bytes)

@[simp] theorem encode_length (message : ClearingDataDealer) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length, HedgeSpec.encode_length, ClearingOperationMode.encode_length]

theorem encode_length_pos (message : ClearingDataDealer) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingDataDealer) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HedgeSpec.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingOperationMode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingDataDealer

/-- Owner Data Dealer: 71 bytes -/
structure OwnerDataDealer where
  clientOrderId : Alpha 20
  poundSign : Alpha 1
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace OwnerDataDealer

def encode (message : OwnerDataDealer) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.poundSign
    ++ (Alpha.encode message.memo))

def decode (bytes : List UInt8) : Option (OwnerDataDealer × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (poundSign, bytes) ← Alpha.decode 1 bytes
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ clientOrderId, poundSign, memo }, bytes)

@[simp] theorem encode_length (message : OwnerDataDealer) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OwnerDataDealer) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OwnerDataDealer) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OwnerDataDealer

/-- Directed Order Acceptation: 200 bytes -/
structure DirectedOrderAcceptation where
  group : Alpha 2
  instrument : Alpha 4
  referencedOrderId : Alpha 8
  auctionStartingPrice : Alpha 10
  clearingDataDealer : ClearingDataDealer
  ownerDataDealer : OwnerDataDealer
  additionalPrice : Alpha 10
  quantityTermQuantityTerm1 : QuantityTermQuantityTerm1
  postTradingInstruction : Alpha 50
  additionalQuantityQuantity8 : Alpha 8
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace DirectedOrderAcceptation

def encode (message : DirectedOrderAcceptation) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.referencedOrderId
    ++ (Alpha.encode message.auctionStartingPrice
    ++ (ClearingDataDealer.encode message.clearingDataDealer
    ++ (OwnerDataDealer.encode message.ownerDataDealer
    ++ (Alpha.encode message.additionalPrice
    ++ (QuantityTermQuantityTerm1.encode message.quantityTermQuantityTerm1
    ++ (Alpha.encode message.postTradingInstruction
    ++ (Alpha.encode message.additionalQuantityQuantity8
    ++ (Alpha.encode message.additionalClientMemo))))))))))

def decode (bytes : List UInt8) : Option (DirectedOrderAcceptation × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (referencedOrderId, bytes) ← Alpha.decode 8 bytes
  let (auctionStartingPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingDataDealer, bytes) ← ClearingDataDealer.decode bytes
  let (ownerDataDealer, bytes) ← OwnerDataDealer.decode bytes
  let (additionalPrice, bytes) ← Alpha.decode 10 bytes
  let (quantityTermQuantityTerm1, bytes) ← QuantityTermQuantityTerm1.decode bytes
  let (postTradingInstruction, bytes) ← Alpha.decode 50 bytes
  let (additionalQuantityQuantity8, bytes) ← Alpha.decode 8 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ group, instrument, referencedOrderId, auctionStartingPrice, clearingDataDealer, ownerDataDealer, additionalPrice, quantityTermQuantityTerm1, postTradingInstruction, additionalQuantityQuantity8, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : DirectedOrderAcceptation) : (encode message).length = 200 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ClearingDataDealer.encode_length, OwnerDataDealer.encode_length, QuantityTermQuantityTerm1.encode_length]

theorem encode_length_pos (message : DirectedOrderAcceptation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DirectedOrderAcceptation) (rest : List UInt8) :
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
  rw [List.append_assoc, ClearingDataDealer.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerDataDealer.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantityTermQuantityTerm1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DirectedOrderAcceptation

/-- Order Entry: 221 bytes -/
structure OrderEntry where
  group : Alpha 2
  instrument : Alpha 4
  priceType : PriceType
  verbSide : VerbSide
  quantity : Alpha 8
  price : Alpha 10
  specialPriceTerm : SpecialPriceTerm
  fillerMustBeBlankString1010 : Alpha 10
  quantityTermQuantityTerm1 : QuantityTermQuantityTerm1
  additionalQuantityAdditionalQuantity8 : Alpha 8
  durationType : DurationType
  gtdDate : Alpha 8
  executingParticipant : Alpha 4
  imlHandling : Alpha 1
  clearingData : ClearingData
  ownerData : OwnerData
  postTradingInstructions : Alpha 50
  additionalClientMemo : Alpha 16
  fillerMustBeBlank2String44 : Alpha 4
  deriving DecidableEq, Repr

namespace OrderEntry

def encode (message : OrderEntry) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (PriceType.encode message.priceType
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (SpecialPriceTerm.encode message.specialPriceTerm
    ++ (Alpha.encode message.fillerMustBeBlankString1010
    ++ (QuantityTermQuantityTerm1.encode message.quantityTermQuantityTerm1
    ++ (Alpha.encode message.additionalQuantityAdditionalQuantity8
    ++ (DurationType.encode message.durationType
    ++ (Alpha.encode message.gtdDate
    ++ (Alpha.encode message.executingParticipant
    ++ (Alpha.encode message.imlHandling
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.postTradingInstructions
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlank2String44))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderEntry × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (specialPriceTerm, bytes) ← SpecialPriceTerm.decode bytes
  let (fillerMustBeBlankString1010, bytes) ← Alpha.decode 10 bytes
  let (quantityTermQuantityTerm1, bytes) ← QuantityTermQuantityTerm1.decode bytes
  let (additionalQuantityAdditionalQuantity8, bytes) ← Alpha.decode 8 bytes
  let (durationType, bytes) ← DurationType.decode bytes
  let (gtdDate, bytes) ← Alpha.decode 8 bytes
  let (executingParticipant, bytes) ← Alpha.decode 4 bytes
  let (imlHandling, bytes) ← Alpha.decode 1 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (postTradingInstructions, bytes) ← Alpha.decode 50 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlank2String44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, priceType, verbSide, quantity, price, specialPriceTerm, fillerMustBeBlankString1010, quantityTermQuantityTerm1, additionalQuantityAdditionalQuantity8, durationType, gtdDate, executingParticipant, imlHandling, clearingData, ownerData, postTradingInstructions, additionalClientMemo, fillerMustBeBlank2String44 }, bytes)

@[simp] theorem encode_length (message : OrderEntry) : (encode message).length = 221 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, PriceType.encode_length, VerbSide.encode_length, SpecialPriceTerm.encode_length, QuantityTermQuantityTerm1.encode_length, DurationType.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialPriceTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantityTermQuantityTerm1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DurationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderEntry

/-- Improvement Order Entry: 210 bytes -/
structure ImprovementOrderEntry where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySign : Alpha 1
  quantity : Alpha 8
  price : Alpha 10
  auctionId : Alpha 6
  fillerString1717 : Alpha 17
  clearingData : ClearingData
  ownerData : OwnerData
  postTradingInstructions : Alpha 50
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  deriving DecidableEq, Repr

namespace ImprovementOrderEntry

def encode (message : ImprovementOrderEntry) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantitySign
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.auctionId
    ++ (Alpha.encode message.fillerString1717
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.postTradingInstructions
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44))))))))))))

def decode (bytes : List UInt8) : Option (ImprovementOrderEntry × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySign, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (fillerString1717, bytes) ← Alpha.decode 17 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (postTradingInstructions, bytes) ← Alpha.decode 50 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, verbSide, quantitySign, quantity, price, auctionId, fillerString1717, clearingData, ownerData, postTradingInstructions, additionalClientMemo, fillerMustBeBlankString44 }, bytes)

@[simp] theorem encode_length (message : ImprovementOrderEntry) : (encode message).length = 210 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : ImprovementOrderEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImprovementOrderEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ImprovementOrderEntry

/-- Order Modification: 230 bytes -/
structure OrderModification where
  group : Alpha 2
  instrument : Alpha 4
  priceType : PriceType
  verbSide : VerbSide
  quantitySign : Alpha 1
  quantity : Alpha 8
  price : Alpha 10
  specialPriceTerm : SpecialPriceTerm
  fillerMustBeBlankString1010 : Alpha 10
  fillerMustBeBlank2String11 : Alpha 1
  fillerMustBeBlank3String88 : Alpha 8
  durationType : DurationType
  gtdDate : Alpha 8
  firmId : Alpha 4
  imlHandling : Alpha 1
  modifiedOrderId : Alpha 8
  clearingData : ClearingData
  ownerData : OwnerData
  postTradingInstruction : Alpha 50
  additionalClientMemo : Alpha 16
  fillerMustBeBlank4 : Alpha 4
  deriving DecidableEq, Repr

namespace OrderModification

def encode (message : OrderModification) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (PriceType.encode message.priceType
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantitySign
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (SpecialPriceTerm.encode message.specialPriceTerm
    ++ (Alpha.encode message.fillerMustBeBlankString1010
    ++ (Alpha.encode message.fillerMustBeBlank2String11
    ++ (Alpha.encode message.fillerMustBeBlank3String88
    ++ (DurationType.encode message.durationType
    ++ (Alpha.encode message.gtdDate
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.imlHandling
    ++ (Alpha.encode message.modifiedOrderId
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.postTradingInstruction
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlank4))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderModification × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySign, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (specialPriceTerm, bytes) ← SpecialPriceTerm.decode bytes
  let (fillerMustBeBlankString1010, bytes) ← Alpha.decode 10 bytes
  let (fillerMustBeBlank2String11, bytes) ← Alpha.decode 1 bytes
  let (fillerMustBeBlank3String88, bytes) ← Alpha.decode 8 bytes
  let (durationType, bytes) ← DurationType.decode bytes
  let (gtdDate, bytes) ← Alpha.decode 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (imlHandling, bytes) ← Alpha.decode 1 bytes
  let (modifiedOrderId, bytes) ← Alpha.decode 8 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (postTradingInstruction, bytes) ← Alpha.decode 50 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlank4, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, priceType, verbSide, quantitySign, quantity, price, specialPriceTerm, fillerMustBeBlankString1010, fillerMustBeBlank2String11, fillerMustBeBlank3String88, durationType, gtdDate, firmId, imlHandling, modifiedOrderId, clearingData, ownerData, postTradingInstruction, additionalClientMemo, fillerMustBeBlank4 }, bytes)

@[simp] theorem encode_length (message : OrderModification) : (encode message).length = 230 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, PriceType.encode_length, VerbSide.encode_length, SpecialPriceTerm.encode_length, DurationType.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderModification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialPriceTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DurationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModification

/-- New Complex Order Instrument Occurrence: 16 bytes -/
structure NewComplexOrderInstrumentOccurrence where
  legGroup : Alpha 2
  legInstrumentId : Alpha 4
  legVerb : LegVerb
  fillerMustBeSpaces : Alpha 1
  legQuantityRatio : Alpha 8
  deriving DecidableEq, Repr

namespace NewComplexOrderInstrumentOccurrence

def encode (message : NewComplexOrderInstrumentOccurrence) : List UInt8 :=
  Alpha.encode message.legGroup
    ++ (Alpha.encode message.legInstrumentId
    ++ (LegVerb.encode message.legVerb
    ++ (Alpha.encode message.fillerMustBeSpaces
    ++ (Alpha.encode message.legQuantityRatio))))

def decode (bytes : List UInt8) : Option (NewComplexOrderInstrumentOccurrence × List UInt8) := do
  let (legGroup, bytes) ← Alpha.decode 2 bytes
  let (legInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (legVerb, bytes) ← LegVerb.decode bytes
  let (fillerMustBeSpaces, bytes) ← Alpha.decode 1 bytes
  let (legQuantityRatio, bytes) ← Alpha.decode 8 bytes
  pure ({ legGroup, legInstrumentId, legVerb, fillerMustBeSpaces, legQuantityRatio }, bytes)

@[simp] theorem encode_length (message : NewComplexOrderInstrumentOccurrence) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LegVerb.encode_length]

theorem encode_length_pos (message : NewComplexOrderInstrumentOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewComplexOrderInstrumentOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LegVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewComplexOrderInstrumentOccurrence

/-- New Complex Order Instrument -/
structure NewComplexOrderInstrument where
  enabledYYesNNo : EnabledYYesNNo
  newComplexOrderInstrumentOccurrence : Digited 2 NewComplexOrderInstrumentOccurrence
  deriving DecidableEq, Repr

namespace NewComplexOrderInstrument

def encode (message : NewComplexOrderInstrument) : List UInt8 :=
  EnabledYYesNNo.encode message.enabledYYesNNo
    ++ (encodeDigits 2 message.newComplexOrderInstrumentOccurrence.val.length
    ++ (encodeMany NewComplexOrderInstrumentOccurrence.encode message.newComplexOrderInstrumentOccurrence.val))

def decode (bytes : List UInt8) : Option (NewComplexOrderInstrument × List UInt8) := do
  let (enabledYYesNNo, bytes) ← EnabledYYesNNo.decode bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (newComplexOrderInstrumentOccurrence_, bytes) ← decodeMany NewComplexOrderInstrumentOccurrence.decode numberOfLegs bytes
  if fits_newComplexOrderInstrumentOccurrence : newComplexOrderInstrumentOccurrence_.length < 10 ^ 2 then
    pure ({ enabledYYesNNo, newComplexOrderInstrumentOccurrence := ⟨newComplexOrderInstrumentOccurrence_, fits_newComplexOrderInstrumentOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewComplexOrderInstrument) : (encode message).length > 0 := by
  unfold encode
  simp only [EnabledYYesNNo.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewComplexOrderInstrument) : (encode message).length ≤ 1587 := by
  have bound_newComplexOrderInstrumentOccurrence := message.newComplexOrderInstrumentOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, EnabledYYesNNo.encode_length, encodeDigits_length, encodeMany_length_const NewComplexOrderInstrumentOccurrence.encode 16 NewComplexOrderInstrumentOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : NewComplexOrderInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, EnabledYYesNNo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.newComplexOrderInstrumentOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany NewComplexOrderInstrumentOccurrence.encode NewComplexOrderInstrumentOccurrence.decode NewComplexOrderInstrumentOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newComplexOrderInstrumentOccurrence.length_lt]
  rfl

end NewComplexOrderInstrument

/-- Complex Order Auction Entry Occurrence: 16 bytes -/
structure ComplexOrderAuctionEntryOccurrence where
  legGroup : Alpha 2
  legInstrument : Alpha 4
  tradeLegPrice : Alpha 10
  deriving DecidableEq, Repr

namespace ComplexOrderAuctionEntryOccurrence

def encode (message : ComplexOrderAuctionEntryOccurrence) : List UInt8 :=
  Alpha.encode message.legGroup
    ++ (Alpha.encode message.legInstrument
    ++ (Alpha.encode message.tradeLegPrice))

def decode (bytes : List UInt8) : Option (ComplexOrderAuctionEntryOccurrence × List UInt8) := do
  let (legGroup, bytes) ← Alpha.decode 2 bytes
  let (legInstrument, bytes) ← Alpha.decode 4 bytes
  let (tradeLegPrice, bytes) ← Alpha.decode 10 bytes
  pure ({ legGroup, legInstrument, tradeLegPrice }, bytes)

@[simp] theorem encode_length (message : ComplexOrderAuctionEntryOccurrence) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ComplexOrderAuctionEntryOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderAuctionEntryOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexOrderAuctionEntryOccurrence

/-- Complex Order Auction Entry -/
structure ComplexOrderAuctionEntry where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantity : Alpha 8
  price : Alpha 10
  buyingClearingData : BuyingClearingData
  sellingClearingData : SellingClearingData
  buyingOwnerData : BuyingOwnerData
  sellingOwnerData : SellingOwnerData
  imlHandling : Alpha 1
  specialPriceTerm : SpecialPriceTerm
  additionalPrice : Alpha 10
  quantityTermQuantitySign1 : Alpha 1
  additionalQuantityQuantity8 : Alpha 8
  buyingPostTradingInstruction : Alpha 50
  sellingPostTradingInstruction : Alpha 50
  buyingAdditionalClientMemo : Alpha 16
  sellingAdditionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  complexOrderAuctionEntryOccurrence : Digited 2 ComplexOrderAuctionEntryOccurrence
  deriving DecidableEq, Repr

namespace ComplexOrderAuctionEntry

def encode (message : ComplexOrderAuctionEntry) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (BuyingClearingData.encode message.buyingClearingData
    ++ (SellingClearingData.encode message.sellingClearingData
    ++ (BuyingOwnerData.encode message.buyingOwnerData
    ++ (SellingOwnerData.encode message.sellingOwnerData
    ++ (Alpha.encode message.imlHandling
    ++ (SpecialPriceTerm.encode message.specialPriceTerm
    ++ (Alpha.encode message.additionalPrice
    ++ (Alpha.encode message.quantityTermQuantitySign1
    ++ (Alpha.encode message.additionalQuantityQuantity8
    ++ (Alpha.encode message.buyingPostTradingInstruction
    ++ (Alpha.encode message.sellingPostTradingInstruction
    ++ (Alpha.encode message.buyingAdditionalClientMemo
    ++ (Alpha.encode message.sellingAdditionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44
    ++ (encodeDigits 2 message.complexOrderAuctionEntryOccurrence.val.length
    ++ (encodeMany ComplexOrderAuctionEntryOccurrence.encode message.complexOrderAuctionEntryOccurrence.val))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderAuctionEntry × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (buyingClearingData, bytes) ← BuyingClearingData.decode bytes
  let (sellingClearingData, bytes) ← SellingClearingData.decode bytes
  let (buyingOwnerData, bytes) ← BuyingOwnerData.decode bytes
  let (sellingOwnerData, bytes) ← SellingOwnerData.decode bytes
  let (imlHandling, bytes) ← Alpha.decode 1 bytes
  let (specialPriceTerm, bytes) ← SpecialPriceTerm.decode bytes
  let (additionalPrice, bytes) ← Alpha.decode 10 bytes
  let (quantityTermQuantitySign1, bytes) ← Alpha.decode 1 bytes
  let (additionalQuantityQuantity8, bytes) ← Alpha.decode 8 bytes
  let (buyingPostTradingInstruction, bytes) ← Alpha.decode 50 bytes
  let (sellingPostTradingInstruction, bytes) ← Alpha.decode 50 bytes
  let (buyingAdditionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (sellingAdditionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  let (nbLegs, bytes) ← decodeDigits 2 bytes
  let (complexOrderAuctionEntryOccurrence_, bytes) ← decodeMany ComplexOrderAuctionEntryOccurrence.decode nbLegs bytes
  if fits_complexOrderAuctionEntryOccurrence : complexOrderAuctionEntryOccurrence_.length < 10 ^ 2 then
    pure ({ group, instrument, verbSide, quantity, price, buyingClearingData, sellingClearingData, buyingOwnerData, sellingOwnerData, imlHandling, specialPriceTerm, additionalPrice, quantityTermQuantitySign1, additionalQuantityQuantity8, buyingPostTradingInstruction, sellingPostTradingInstruction, buyingAdditionalClientMemo, sellingAdditionalClientMemo, fillerMustBeBlankString44, complexOrderAuctionEntryOccurrence := ⟨complexOrderAuctionEntryOccurrence_, fits_complexOrderAuctionEntryOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexOrderAuctionEntry) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexOrderAuctionEntry) : (encode message).length ≤ 1950 := by
  have bound_complexOrderAuctionEntryOccurrence := message.complexOrderAuctionEntryOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, VerbSide.encode_length, BuyingClearingData.encode_length, SellingClearingData.encode_length, BuyingOwnerData.encode_length, SellingOwnerData.encode_length, SpecialPriceTerm.encode_length, encodeDigits_length, encodeMany_length_const ComplexOrderAuctionEntryOccurrence.encode 16 ComplexOrderAuctionEntryOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexOrderAuctionEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyingClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellingClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyingOwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellingOwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialPriceTerm.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.complexOrderAuctionEntryOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany ComplexOrderAuctionEntryOccurrence.encode ComplexOrderAuctionEntryOccurrence.decode ComplexOrderAuctionEntryOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexOrderAuctionEntryOccurrence.length_lt]
  rfl

end ComplexOrderAuctionEntry

/-- Executing Participant Connection: 0 bytes -/
structure ExecutingParticipantConnection where
  deriving DecidableEq, Repr

namespace ExecutingParticipantConnection

def encode (_ : ExecutingParticipantConnection) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ExecutingParticipantConnection × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ExecutingParticipantConnection) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ExecutingParticipantConnection) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ExecutingParticipantConnection

/-- Executing Participant Disconnection: 0 bytes -/
structure ExecutingParticipantDisconnection where
  deriving DecidableEq, Repr

namespace ExecutingParticipantDisconnection

def encode (_ : ExecutingParticipantDisconnection) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ExecutingParticipantDisconnection × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ExecutingParticipantDisconnection) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ExecutingParticipantDisconnection) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ExecutingParticipantDisconnection

/-- Market Maker Protection Subscription: 3 bytes -/
structure MarketMakerProtectionSubscription where
  group : Alpha 2
  protectionTypeAdvancedNormal : ProtectionTypeAdvancedNormal
  deriving DecidableEq, Repr

namespace MarketMakerProtectionSubscription

def encode (message : MarketMakerProtectionSubscription) : List UInt8 :=
  Alpha.encode message.group
    ++ (ProtectionTypeAdvancedNormal.encode message.protectionTypeAdvancedNormal)

def decode (bytes : List UInt8) : Option (MarketMakerProtectionSubscription × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (protectionTypeAdvancedNormal, bytes) ← ProtectionTypeAdvancedNormal.decode bytes
  pure ({ group, protectionTypeAdvancedNormal }, bytes)

@[simp] theorem encode_length (message : MarketMakerProtectionSubscription) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ProtectionTypeAdvancedNormal.encode_length]

theorem encode_length_pos (message : MarketMakerProtectionSubscription) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketMakerProtectionSubscription) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ProtectionTypeAdvancedNormal.decode_encode, some_bind]
  rfl

end MarketMakerProtectionSubscription

/-- Request For Quote: 14 bytes -/
structure RequestForQuote where
  group : Alpha 2
  instrument : Alpha 4
  quantity1 : Alpha 8
  deriving DecidableEq, Repr

namespace RequestForQuote

def encode (message : RequestForQuote) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.quantity1))

def decode (bytes : List UInt8) : Option (RequestForQuote × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (quantity1, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, quantity1 }, bytes)

@[simp] theorem encode_length (message : RequestForQuote) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : RequestForQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RequestForQuote

/-- Order Cancellation: 14 bytes -/
structure OrderCancellation where
  group : Alpha 2
  instrument : Alpha 4
  cancelledOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace OrderCancellation

def encode (message : OrderCancellation) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.cancelledOrderId))

def decode (bytes : List UInt8) : Option (OrderCancellation × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (cancelledOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, cancelledOrderId }, bytes)

@[simp] theorem encode_length (message : OrderCancellation) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellation

/-- Improvement Order Cancellation: 14 bytes -/
structure ImprovementOrderCancellation where
  group : Alpha 2
  instrument : Alpha 4
  cancelledOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace ImprovementOrderCancellation

def encode (message : ImprovementOrderCancellation) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.cancelledOrderId))

def decode (bytes : List UInt8) : Option (ImprovementOrderCancellation × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (cancelledOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, cancelledOrderId }, bytes)

@[simp] theorem encode_length (message : ImprovementOrderCancellation) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ImprovementOrderCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImprovementOrderCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ImprovementOrderCancellation

/-- Any Firm Message, selected by Message Type -/
inductive FirmMessage where
  | userConnection (message : UserConnection) -- "TC" 0x5443
  | userDisconnection (message : UserDisconnection) -- "TD" 0x5444
  | disconnectionInstruction (message : DisconnectionInstruction) -- "TA" 0x5441
  | heartbeatResponse (message : HeartbeatResponse) -- "TI" 0x5449
  | bulkQuoteData (message : BulkQuoteData) -- "BD" 0x4244
  | globalCancellation (message : GlobalCancellation) -- "GC" 0x4743
  | userGlobalCancellation (message : UserGlobalCancellation) -- "GZ" 0x475A
  | directedRoutedOrderRejectionAndQuote (message : DirectedRoutedOrderRejectionAndQuote) -- "KQ" 0x4B51
  | auctionEntry (message : AuctionEntry) -- "OA" 0x4F41
  | directedOrderAcceptation (message : DirectedOrderAcceptation) -- "OD" 0x4F44
  | orderEntry (message : OrderEntry) -- "OE" 0x4F45
  | improvementOrderEntry (message : ImprovementOrderEntry) -- "OI" 0x4F49
  | orderModification (message : OrderModification) -- "OM" 0x4F4D
  | newComplexOrderInstrument (message : NewComplexOrderInstrument) -- "ON" 0x4F4E
  | complexOrderAuctionEntry (message : ComplexOrderAuctionEntry) -- "OT" 0x4F54
  | executingParticipantConnection (message : ExecutingParticipantConnection) -- "RE" 0x5245
  | executingParticipantDisconnection (message : ExecutingParticipantDisconnection) -- "RF" 0x5246
  | marketMakerProtectionSubscription (message : MarketMakerProtectionSubscription) -- "RP" 0x5250
  | requestForQuote (message : RequestForQuote) -- "RQ" 0x5251
  | orderCancellation (message : OrderCancellation) -- "XE" 0x5845
  | improvementOrderCancellation (message : ImprovementOrderCancellation) -- "XI" 0x5849
  deriving DecidableEq, Repr

namespace FirmMessage

/-- The Message Type each message is sent under -/
def tag : FirmMessage → BitVec 16
  | .userConnection _ => 21571
  | .userDisconnection _ => 21572
  | .disconnectionInstruction _ => 21569
  | .heartbeatResponse _ => 21577
  | .bulkQuoteData _ => 16964
  | .globalCancellation _ => 18243
  | .userGlobalCancellation _ => 18266
  | .directedRoutedOrderRejectionAndQuote _ => 19281
  | .auctionEntry _ => 20289
  | .directedOrderAcceptation _ => 20292
  | .orderEntry _ => 20293
  | .improvementOrderEntry _ => 20297
  | .orderModification _ => 20301
  | .newComplexOrderInstrument _ => 20302
  | .complexOrderAuctionEntry _ => 20308
  | .executingParticipantConnection _ => 21061
  | .executingParticipantDisconnection _ => 21062
  | .marketMakerProtectionSubscription _ => 21072
  | .requestForQuote _ => 21073
  | .orderCancellation _ => 22597
  | .improvementOrderCancellation _ => 22601

def encode : FirmMessage → List UInt8
  | .userConnection message => UserConnection.encode message
  | .userDisconnection message => UserDisconnection.encode message
  | .disconnectionInstruction message => DisconnectionInstruction.encode message
  | .heartbeatResponse message => HeartbeatResponse.encode message
  | .bulkQuoteData message => BulkQuoteData.encode message
  | .globalCancellation message => GlobalCancellation.encode message
  | .userGlobalCancellation message => UserGlobalCancellation.encode message
  | .directedRoutedOrderRejectionAndQuote message => DirectedRoutedOrderRejectionAndQuote.encode message
  | .auctionEntry message => AuctionEntry.encode message
  | .directedOrderAcceptation message => DirectedOrderAcceptation.encode message
  | .orderEntry message => OrderEntry.encode message
  | .improvementOrderEntry message => ImprovementOrderEntry.encode message
  | .orderModification message => OrderModification.encode message
  | .newComplexOrderInstrument message => NewComplexOrderInstrument.encode message
  | .complexOrderAuctionEntry message => ComplexOrderAuctionEntry.encode message
  | .executingParticipantConnection message => ExecutingParticipantConnection.encode message
  | .executingParticipantDisconnection message => ExecutingParticipantDisconnection.encode message
  | .marketMakerProtectionSubscription message => MarketMakerProtectionSubscription.encode message
  | .requestForQuote message => RequestForQuote.encode message
  | .orderCancellation message => OrderCancellation.encode message
  | .improvementOrderCancellation message => ImprovementOrderCancellation.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : FirmMessage) : (encode message).length ≤ 1950 := by
  cases message with
  | userConnection inner =>
    have bound_inner := UserConnection.encode_length_le inner
    simp only [encode]
    omega
  | userDisconnection inner =>
    simp only [encode, UserDisconnection.encode_length]
    omega
  | disconnectionInstruction inner =>
    have bound_inner := DisconnectionInstruction.encode_length_le inner
    simp only [encode]
    omega
  | heartbeatResponse inner =>
    simp only [encode, HeartbeatResponse.encode_length]
    omega
  | bulkQuoteData inner =>
    simp only [encode, BulkQuoteData.encode_length]
    omega
  | globalCancellation inner =>
    simp only [encode, GlobalCancellation.encode_length]
    omega
  | userGlobalCancellation inner =>
    simp only [encode, UserGlobalCancellation.encode_length]
    omega
  | directedRoutedOrderRejectionAndQuote inner =>
    simp only [encode, DirectedRoutedOrderRejectionAndQuote.encode_length]
    omega
  | auctionEntry inner =>
    simp only [encode, AuctionEntry.encode_length]
    omega
  | directedOrderAcceptation inner =>
    simp only [encode, DirectedOrderAcceptation.encode_length]
    omega
  | orderEntry inner =>
    simp only [encode, OrderEntry.encode_length]
    omega
  | improvementOrderEntry inner =>
    simp only [encode, ImprovementOrderEntry.encode_length]
    omega
  | orderModification inner =>
    simp only [encode, OrderModification.encode_length]
    omega
  | newComplexOrderInstrument inner =>
    have bound_inner := NewComplexOrderInstrument.encode_length_le inner
    simp only [encode]
    omega
  | complexOrderAuctionEntry inner =>
    have bound_inner := ComplexOrderAuctionEntry.encode_length_le inner
    simp only [encode]
    omega
  | executingParticipantConnection inner =>
    simp only [encode, ExecutingParticipantConnection.encode_length]
    omega
  | executingParticipantDisconnection inner =>
    simp only [encode, ExecutingParticipantDisconnection.encode_length]
    omega
  | marketMakerProtectionSubscription inner =>
    simp only [encode, MarketMakerProtectionSubscription.encode_length]
    omega
  | requestForQuote inner =>
    simp only [encode, RequestForQuote.encode_length]
    omega
  | orderCancellation inner =>
    simp only [encode, OrderCancellation.encode_length]
    omega
  | improvementOrderCancellation inner =>
    simp only [encode, ImprovementOrderCancellation.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (FirmMessage × List UInt8) :=
  if tag = 21571 then (UserConnection.decode bytes).map fun (message, rest) => (.userConnection message, rest)
  else if tag = 21572 then (UserDisconnection.decode bytes).map fun (message, rest) => (.userDisconnection message, rest)
  else if tag = 21569 then (DisconnectionInstruction.decode bytes).map fun (message, rest) => (.disconnectionInstruction message, rest)
  else if tag = 21577 then (HeartbeatResponse.decode bytes).map fun (message, rest) => (.heartbeatResponse message, rest)
  else if tag = 16964 then (BulkQuoteData.decode bytes).map fun (message, rest) => (.bulkQuoteData message, rest)
  else if tag = 18243 then (GlobalCancellation.decode bytes).map fun (message, rest) => (.globalCancellation message, rest)
  else if tag = 18266 then (UserGlobalCancellation.decode bytes).map fun (message, rest) => (.userGlobalCancellation message, rest)
  else if tag = 19281 then (DirectedRoutedOrderRejectionAndQuote.decode bytes).map fun (message, rest) => (.directedRoutedOrderRejectionAndQuote message, rest)
  else if tag = 20289 then (AuctionEntry.decode bytes).map fun (message, rest) => (.auctionEntry message, rest)
  else if tag = 20292 then (DirectedOrderAcceptation.decode bytes).map fun (message, rest) => (.directedOrderAcceptation message, rest)
  else if tag = 20293 then (OrderEntry.decode bytes).map fun (message, rest) => (.orderEntry message, rest)
  else if tag = 20297 then (ImprovementOrderEntry.decode bytes).map fun (message, rest) => (.improvementOrderEntry message, rest)
  else if tag = 20301 then (OrderModification.decode bytes).map fun (message, rest) => (.orderModification message, rest)
  else if tag = 20302 then (NewComplexOrderInstrument.decode bytes).map fun (message, rest) => (.newComplexOrderInstrument message, rest)
  else if tag = 20308 then (ComplexOrderAuctionEntry.decode bytes).map fun (message, rest) => (.complexOrderAuctionEntry message, rest)
  else if tag = 21061 then (ExecutingParticipantConnection.decode bytes).map fun (message, rest) => (.executingParticipantConnection message, rest)
  else if tag = 21062 then (ExecutingParticipantDisconnection.decode bytes).map fun (message, rest) => (.executingParticipantDisconnection message, rest)
  else if tag = 21072 then (MarketMakerProtectionSubscription.decode bytes).map fun (message, rest) => (.marketMakerProtectionSubscription message, rest)
  else if tag = 21073 then (RequestForQuote.decode bytes).map fun (message, rest) => (.requestForQuote message, rest)
  else if tag = 22597 then (OrderCancellation.decode bytes).map fun (message, rest) => (.orderCancellation message, rest)
  else if tag = 22601 then (ImprovementOrderCancellation.decode bytes).map fun (message, rest) => (.improvementOrderCancellation message, rest)
  else none

@[simp] theorem decode_encode (message : FirmMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end FirmMessage

/-- Firm Packet -/
structure FirmPacket where
  messageLength : BitVec 32
  userTime : Alpha 6
  traderId : Alpha 8
  userSequenceId : Alpha 8
  firmMessage : FirmMessage
  endOfText : BitVec 8
  deriving DecidableEq, Repr

namespace FirmPacket

def encode (message : FirmPacket) : List UInt8 :=
  encodeUIntLE 4 message.messageLength
    ++ (encodeUInt 2 (FirmMessage.tag message.firmMessage)
    ++ (Alpha.encode message.userTime
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.userSequenceId
    ++ (FirmMessage.encode message.firmMessage
    ++ (encodeUInt 1 message.endOfText))))))

def decode (bytes : List UInt8) : Option (FirmPacket × List UInt8) := do
  let (messageLength, bytes) ← decodeUIntLE 4 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (userTime, bytes) ← Alpha.decode 6 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (userSequenceId, bytes) ← Alpha.decode 8 bytes
  let (firmMessage, bytes) ← FirmMessage.decode messageType bytes
  let (endOfText, bytes) ← decodeUInt 1 bytes
  pure ({ messageLength, userTime, traderId, userSequenceId, firmMessage, endOfText }, bytes)

theorem encode_length_pos (message : FirmPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FirmPacket) : (encode message).length ≤ 1979 := by
  unfold encode
  cases message.firmMessage with
  | userConnection inner =>
    have bound_inner := UserConnection.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
    omega
  | userDisconnection inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, UserDisconnection.encode_length]
    omega
  | disconnectionInstruction inner =>
    have bound_inner := DisconnectionInstruction.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
    omega
  | heartbeatResponse inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, HeartbeatResponse.encode_length]
    omega
  | bulkQuoteData inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, BulkQuoteData.encode_length]
    omega
  | globalCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, GlobalCancellation.encode_length]
    omega
  | userGlobalCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, UserGlobalCancellation.encode_length]
    omega
  | directedRoutedOrderRejectionAndQuote inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, DirectedRoutedOrderRejectionAndQuote.encode_length]
    omega
  | auctionEntry inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, AuctionEntry.encode_length]
    omega
  | directedOrderAcceptation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, DirectedOrderAcceptation.encode_length]
    omega
  | orderEntry inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrderEntry.encode_length]
    omega
  | improvementOrderEntry inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ImprovementOrderEntry.encode_length]
    omega
  | orderModification inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrderModification.encode_length]
    omega
  | newComplexOrderInstrument inner =>
    have bound_inner := NewComplexOrderInstrument.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
    omega
  | complexOrderAuctionEntry inner =>
    have bound_inner := ComplexOrderAuctionEntry.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
    omega
  | executingParticipantConnection inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ExecutingParticipantConnection.encode_length]
    omega
  | executingParticipantDisconnection inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ExecutingParticipantDisconnection.encode_length]
    omega
  | marketMakerProtectionSubscription inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, MarketMakerProtectionSubscription.encode_length]
    omega
  | requestForQuote inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, RequestForQuote.encode_length]
    omega
  | orderCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrderCancellation.encode_length]
    omega
  | improvementOrderCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ImprovementOrderCancellation.encode_length]
    omega

@[simp] theorem decode_encode (message : FirmPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FirmMessage.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FirmPacket

end Omi.BoxBoxoptionsSolaorderentrySailV225Firm
