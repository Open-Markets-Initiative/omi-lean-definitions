import Omi.Wire

/-!
# Box Options Market Sola Order Entry v2.25

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Number Of Legs counts New Complex Order Instrument Acknowledgement Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Note: Number Of Quotes In Error counts Bulk Quote Acknowledgement Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 999 could not be written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BoxBoxoptionsSolaorderentrySailV225Exchange

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x45, 0x47, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4F, 0x50, 0x52, 0x54, 0x57, 0x58]

inductive Status where
  | orderCancelledByTheTraderOrAtTheEndOfTheExpositionPhase -- Order Cancelled By The Trader Or At The End Of The Exposition Phase
  | orderHasBeenEliminatedByTheTradingSystemDueToInvalidOutOfLimitsPrice -- Order Has Been Eliminated By The Trading System Due To Invalid Out Of Limits Price
  | theOrderIsADirectedRoutedOrderAndHasBeenReceivedByExecutingParticipant -- The Order Is A Directed Routed Order And Has Been Received By Executing Participant
  | theOrderHasBeenEliminatedByTheTradingSystem -- The Order Has Been Eliminated By The Trading System
  | cancelledBySupervisor -- Cancelled By Supervisor
  | sessionOrderHasBeenCancelledWhenTheParticipantClosesOrLosesHisConnectionToTheSolaTradingSystem -- Session Order Has Been Cancelled When The Participant Closes Or Loses His Connection To The Sola Trading System
  | eliminatedDueToMaximumNbTriggersLimitExceeded -- Eliminated Due To Maximum Nb Triggers Limit Exceeded
  | eliminatedDueToTradeActivityLimitExceeded -- Eliminated Due To Trade Activity Limit Exceeded
  | orderHasBeenSentToTheAwayExchange -- Order Has Been Sent To The Away Exchange
  | cancelledByTheBoxMarketOperationsCenterMoc -- Cancelled By The Box Market Operations Center Moc
  | eliminatedDueToDrillThroughProtection -- Eliminated Due To Drill Through Protection
  | orderIsBeingExposed -- Order Is Being Exposed
  | orderIsEliminatedDueToTradingRestriction -- Order Is Eliminated Due To Trading Restriction
  | eliminatedDueToTradeLimitExceeded -- Eliminated Due To Trade Limit Exceeded
  | cancelPending -- Cancel Pending
  | orderExecutedInFullOrPartiallyAndTheRemainingPartCouldNotBePutInTheOrderBookFillKillTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide -- Order Executed In Full Or Partially And The Remaining Part Could Not Be Put In The Order Book Fill Kill The Guide States No Width For This Type One Character Is Inferred From The Values It States Each Of Which Is One Character Wide
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .orderCancelledByTheTraderOrAtTheEndOfTheExpositionPhase => 0x41
  | .orderHasBeenEliminatedByTheTradingSystemDueToInvalidOutOfLimitsPrice => 0x42
  | .theOrderIsADirectedRoutedOrderAndHasBeenReceivedByExecutingParticipant => 0x44
  | .theOrderHasBeenEliminatedByTheTradingSystem => 0x45
  | .cancelledBySupervisor => 0x47
  | .sessionOrderHasBeenCancelledWhenTheParticipantClosesOrLosesHisConnectionToTheSolaTradingSystem => 0x49
  | .eliminatedDueToMaximumNbTriggersLimitExceeded => 0x4A
  | .eliminatedDueToTradeActivityLimitExceeded => 0x4B
  | .orderHasBeenSentToTheAwayExchange => 0x4C
  | .cancelledByTheBoxMarketOperationsCenterMoc => 0x4D
  | .eliminatedDueToDrillThroughProtection => 0x4F
  | .orderIsBeingExposed => 0x50
  | .orderIsEliminatedDueToTradingRestriction => 0x52
  | .eliminatedDueToTradeLimitExceeded => 0x54
  | .cancelPending => 0x57
  | .orderExecutedInFullOrPartiallyAndTheRemainingPartCouldNotBePutInTheOrderBookFillKillTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x41 then .orderCancelledByTheTraderOrAtTheEndOfTheExpositionPhase
  else if byte = 0x42 then .orderHasBeenEliminatedByTheTradingSystemDueToInvalidOutOfLimitsPrice
  else if byte = 0x44 then .theOrderIsADirectedRoutedOrderAndHasBeenReceivedByExecutingParticipant
  else if byte = 0x45 then .theOrderHasBeenEliminatedByTheTradingSystem
  else if byte = 0x47 then .cancelledBySupervisor
  else if byte = 0x49 then .sessionOrderHasBeenCancelledWhenTheParticipantClosesOrLosesHisConnectionToTheSolaTradingSystem
  else if byte = 0x4A then .eliminatedDueToMaximumNbTriggersLimitExceeded
  else if byte = 0x4B then .eliminatedDueToTradeActivityLimitExceeded
  else if byte = 0x4C then .orderHasBeenSentToTheAwayExchange
  else if byte = 0x4D then .cancelledByTheBoxMarketOperationsCenterMoc
  else if byte = 0x4F then .eliminatedDueToDrillThroughProtection
  else if byte = 0x50 then .orderIsBeingExposed
  else if byte = 0x52 then .orderIsEliminatedDueToTradingRestriction
  else if byte = 0x54 then .eliminatedDueToTradeLimitExceeded
  else if byte = 0x57 then .cancelPending
  else .orderExecutedInFullOrPartiallyAndTheRemainingPartCouldNotBePutInTheOrderBookFillKillTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | orderCancelledByTheTraderOrAtTheEndOfTheExpositionPhase => decide
  | orderHasBeenEliminatedByTheTradingSystemDueToInvalidOutOfLimitsPrice => decide
  | theOrderIsADirectedRoutedOrderAndHasBeenReceivedByExecutingParticipant => decide
  | theOrderHasBeenEliminatedByTheTradingSystem => decide
  | cancelledBySupervisor => decide
  | sessionOrderHasBeenCancelledWhenTheParticipantClosesOrLosesHisConnectionToTheSolaTradingSystem => decide
  | eliminatedDueToMaximumNbTriggersLimitExceeded => decide
  | eliminatedDueToTradeActivityLimitExceeded => decide
  | orderHasBeenSentToTheAwayExchange => decide
  | cancelledByTheBoxMarketOperationsCenterMoc => decide
  | eliminatedDueToDrillThroughProtection => decide
  | orderIsBeingExposed => decide
  | orderIsEliminatedDueToTradingRestriction => decide
  | eliminatedDueToTradeLimitExceeded => decide
  | cancelPending => decide
  | orderExecutedInFullOrPartiallyAndTheRemainingPartCouldNotBePutInTheOrderBookFillKillTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Status) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Status × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Status) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Status) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Status

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
  [0x20, 0x43, 0x47, 0x49]

inductive ClearingOperationMode where
  | noClearingOperation -- No Clearing Operation
  | cmtaClearingMemberTradingAgreementFirmWillBeDefinedInTheClearingDestinationField -- Cmta Clearing Member Trading Agreement Firm Will Be Defined In The Clearing Destination Field
  | giveUpFirmWillBeDefinedInTheClearingDestinationField -- Give Up Firm Will Be Defined In The Clearing Destination Field
  | bothCmtaAndGiveUpFirmsWillBeDefinedInThePostTradingInstructionFieldTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide -- Both Cmta And Give Up Firms Will Be Defined In The Post Trading Instruction Field The Guide States No Width For This Type One Character Is Inferred From The Values It States Each Of Which Is One Character Wide
  | unlisted (byte : { byte : UInt8 // byte ∉ ClearingOperationMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClearingOperationMode

def toByte : ClearingOperationMode → UInt8
  | .noClearingOperation => 0x20
  | .cmtaClearingMemberTradingAgreementFirmWillBeDefinedInTheClearingDestinationField => 0x43
  | .giveUpFirmWillBeDefinedInTheClearingDestinationField => 0x47
  | .bothCmtaAndGiveUpFirmsWillBeDefinedInThePostTradingInstructionFieldTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClearingOperationMode :=
  if byte = 0x20 then .noClearingOperation
  else if byte = 0x43 then .cmtaClearingMemberTradingAgreementFirmWillBeDefinedInTheClearingDestinationField
  else if byte = 0x47 then .giveUpFirmWillBeDefinedInTheClearingDestinationField
  else .bothCmtaAndGiveUpFirmsWillBeDefinedInThePostTradingInstructionFieldTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide

def ofByte (byte : UInt8) : ClearingOperationMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClearingOperationMode) : ofByte value.toByte = value := by
  cases value with
  | noClearingOperation => decide
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

/-- Type Of Cancellation Only Q Quotes Only Can Be Returned: one byte code -/
def TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.codes : List UInt8 :=
  [0x41, 0x4C, 0x4F, 0x51]

inductive TypeOfCancellationOnlyQQuotesOnlyCanBeReturned where
  | all -- All
  | locked -- Locked
  | ordersOnly -- Orders Only
  | quotesOnly -- Quotes Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfCancellationOnlyQQuotesOnlyCanBeReturned

def toByte : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned → UInt8
  | .all => 0x41
  | .locked => 0x4C
  | .ordersOnly => 0x4F
  | .quotesOnly => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned :=
  if byte = 0x41 then .all
  else if byte = 0x4C then .locked
  else if byte = 0x4F then .ordersOnly
  else .quotesOnly

def ofByte (byte : UInt8) : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | locked => decide
  | ordersOnly => decide
  | quotesOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfCancellationOnlyQQuotesOnlyCanBeReturned × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfCancellationOnlyQQuotesOnlyCanBeReturned

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

/-- Trader Lock Out: one byte code -/
def TraderLockOut.codes : List UInt8 :=
  [0x4C, 0x55]

inductive TraderLockOut where
  | locked -- Locked
  | unlockedTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide -- Unlocked The Guide States No Width For This Type One Character Is Inferred From The Values It States Each Of Which Is One Character Wide
  | unlisted (byte : { byte : UInt8 // byte ∉ TraderLockOut.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TraderLockOut

def toByte : TraderLockOut → UInt8
  | .locked => 0x4C
  | .unlockedTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TraderLockOut :=
  if byte = 0x4C then .locked
  else .unlockedTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide

def ofByte (byte : UInt8) : TraderLockOut :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TraderLockOut) : ofByte value.toByte = value := by
  cases value with
  | locked => decide
  | unlockedTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TraderLockOut) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TraderLockOut × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TraderLockOut) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TraderLockOut) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TraderLockOut

/-- Risk Team Lock Out: one byte code -/
def RiskTeamLockOut.codes : List UInt8 :=
  [0x4C, 0x55]

inductive RiskTeamLockOut where
  | locked -- Locked
  | unlockedTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide -- Unlocked The Guide States No Width For This Type One Character Is Inferred From The Values It States Each Of Which Is One Character Wide
  | unlisted (byte : { byte : UInt8 // byte ∉ RiskTeamLockOut.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RiskTeamLockOut

def toByte : RiskTeamLockOut → UInt8
  | .locked => 0x4C
  | .unlockedTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RiskTeamLockOut :=
  if byte = 0x4C then .locked
  else .unlockedTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide

def ofByte (byte : UInt8) : RiskTeamLockOut :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RiskTeamLockOut) : ofByte value.toByte = value := by
  cases value with
  | locked => decide
  | unlockedTheGuideStatesNoWidthForThisTypeOneCharacterIsInferredFromTheValuesItStatesEachOfWhichIsOneCharacterWide => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RiskTeamLockOut) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RiskTeamLockOut × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RiskTeamLockOut) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RiskTeamLockOut) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RiskTeamLockOut

/-- Group State: one byte code -/
def GroupState.codes : List UInt8 :=
  [0x42, 0x43, 0x46, 0x49, 0x4D, 0x4E, 0x4F, 0x50, 0x53, 0x5A]

inductive GroupState where
  | postSession -- Post Session
  | consultationStart -- Consultation Start
  | consultationEnd -- Consultation End
  | prohibited -- Prohibited
  | minibatch -- Minibatch
  | marketOperationCenterIntervention -- Market Operation Center Intervention
  | opening -- Opening
  | preopening -- Preopening
  | continuousTradingSession -- Continuous Trading Session
  | interrupted -- Interrupted
  | unlisted (byte : { byte : UInt8 // byte ∉ GroupState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GroupState

def toByte : GroupState → UInt8
  | .postSession => 0x42
  | .consultationStart => 0x43
  | .consultationEnd => 0x46
  | .prohibited => 0x49
  | .minibatch => 0x4D
  | .marketOperationCenterIntervention => 0x4E
  | .opening => 0x4F
  | .preopening => 0x50
  | .continuousTradingSession => 0x53
  | .interrupted => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GroupState :=
  if byte = 0x42 then .postSession
  else if byte = 0x43 then .consultationStart
  else if byte = 0x46 then .consultationEnd
  else if byte = 0x49 then .prohibited
  else if byte = 0x4D then .minibatch
  else if byte = 0x4E then .marketOperationCenterIntervention
  else if byte = 0x4F then .opening
  else if byte = 0x50 then .preopening
  else if byte = 0x53 then .continuousTradingSession
  else .interrupted

def ofByte (byte : UInt8) : GroupState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GroupState) : ofByte value.toByte = value := by
  cases value with
  | postSession => decide
  | consultationStart => decide
  | consultationEnd => decide
  | prohibited => decide
  | minibatch => decide
  | marketOperationCenterIntervention => decide
  | opening => decide
  | preopening => decide
  | continuousTradingSession => decide
  | interrupted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GroupState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GroupState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GroupState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : GroupState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GroupState

/-- Special Trade Indicator: one byte code -/
def SpecialTradeIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x4C, 0x4F, 0x53, 0x52, 0x44, 0x67]

inductive SpecialTradeIndicator where
  | asOfTrade -- As Of Trade
  | blockTrade -- Block Trade
  | lateTrade -- Late Trade
  | hiddenTrade -- Hidden Trade
  | sizeAdjustmentTrade -- Size Adjustment Trade
  | floorTrade -- Floor Trade
  | customerCrossOrderOrQualifiedContingentCrossOrderAppliesToSolicitationFacilitationAndFloorTradeOnly -- Customer Cross Order Or Qualified Contingent Cross Order Applies To Solicitation Facilitation And Floor Trade Only
  | contingentTradeTradeWasNotControlledAgainstTheNbbo -- Contingent Trade Trade Was Not Controlled Against The Nbbo
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialTradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialTradeIndicator

def toByte : SpecialTradeIndicator → UInt8
  | .asOfTrade => 0x41
  | .blockTrade => 0x42
  | .lateTrade => 0x4C
  | .hiddenTrade => 0x4F
  | .sizeAdjustmentTrade => 0x53
  | .floorTrade => 0x52
  | .customerCrossOrderOrQualifiedContingentCrossOrderAppliesToSolicitationFacilitationAndFloorTradeOnly => 0x44
  | .contingentTradeTradeWasNotControlledAgainstTheNbbo => 0x67
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialTradeIndicator :=
  if byte = 0x41 then .asOfTrade
  else if byte = 0x42 then .blockTrade
  else if byte = 0x4C then .lateTrade
  else if byte = 0x4F then .hiddenTrade
  else if byte = 0x53 then .sizeAdjustmentTrade
  else if byte = 0x52 then .floorTrade
  else if byte = 0x44 then .customerCrossOrderOrQualifiedContingentCrossOrderAppliesToSolicitationFacilitationAndFloorTradeOnly
  else .contingentTradeTradeWasNotControlledAgainstTheNbbo

def ofByte (byte : UInt8) : SpecialTradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialTradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | asOfTrade => decide
  | blockTrade => decide
  | lateTrade => decide
  | hiddenTrade => decide
  | sizeAdjustmentTrade => decide
  | floorTrade => decide
  | customerCrossOrderOrQualifiedContingentCrossOrderAppliesToSolicitationFacilitationAndFloorTradeOnly => decide
  | contingentTradeTradeWasNotControlledAgainstTheNbbo => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialTradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialTradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialTradeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SpecialTradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialTradeIndicator

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

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x46, 0x4D, 0x4F]

inductive TradeType where
  | tradedDuringAGuaranteedAuction -- Traded During A Guaranteed Auction
  | solicitationAuction -- Solicitation Auction
  | facilitationAuction -- Facilitation Auction
  | tradedDuringContinuousTradingFollowingFifoAlgorithm -- Traded During Continuous Trading Following Fifo Algorithm
  | tradeEnteredByMarketOperations -- Trade Entered By Market Operations
  | tradedDuringOpening -- Traded During Opening
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .tradedDuringAGuaranteedAuction => 0x41
  | .solicitationAuction => 0x42
  | .facilitationAuction => 0x43
  | .tradedDuringContinuousTradingFollowingFifoAlgorithm => 0x46
  | .tradeEnteredByMarketOperations => 0x4D
  | .tradedDuringOpening => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x41 then .tradedDuringAGuaranteedAuction
  else if byte = 0x42 then .solicitationAuction
  else if byte = 0x43 then .facilitationAuction
  else if byte = 0x46 then .tradedDuringContinuousTradingFollowingFifoAlgorithm
  else if byte = 0x4D then .tradeEnteredByMarketOperations
  else .tradedDuringOpening

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | tradedDuringAGuaranteedAuction => decide
  | solicitationAuction => decide
  | facilitationAuction => decide
  | tradedDuringContinuousTradingFollowingFifoAlgorithm => decide
  | tradeEnteredByMarketOperations => decide
  | tradedDuringOpening => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Liquidity Status: one byte code -/
def LiquidityStatus.codes : List UInt8 :=
  [0x4D, 0x54]

inductive LiquidityStatus where
  | maker -- Maker
  | taker -- Taker
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityStatus

def toByte : LiquidityStatus → UInt8
  | .maker => 0x4D
  | .taker => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityStatus :=
  if byte = 0x4D then .maker
  else .taker

def ofByte (byte : UInt8) : LiquidityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityStatus) : ofByte value.toByte = value := by
  cases value with
  | maker => decide
  | taker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityStatus

/-- Strategy Verb Side: one byte code -/
def StrategyVerbSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive StrategyVerbSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyVerbSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyVerbSide

def toByte : StrategyVerbSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyVerbSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : StrategyVerbSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyVerbSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyVerbSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyVerbSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyVerbSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrategyVerbSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyVerbSide

/-- Counterpart Account Type: one byte code -/
def CounterpartAccountType.codes : List UInt8 :=
  [0x36, 0x37, 0x38, 0x54, 0x57, 0x58]

inductive CounterpartAccountType where
  | publicCustomer -- Public Customer
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealerClearedAsCustomer -- Broker Dealer Cleared As Customer
  | awayMarketMaker -- Away Market Maker
  | unlisted (byte : { byte : UInt8 // byte ∉ CounterpartAccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CounterpartAccountType

def toByte : CounterpartAccountType → UInt8
  | .publicCustomer => 0x36
  | .brokerDealer => 0x37
  | .marketMaker => 0x38
  | .professionalCustomer => 0x54
  | .brokerDealerClearedAsCustomer => 0x57
  | .awayMarketMaker => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CounterpartAccountType :=
  if byte = 0x36 then .publicCustomer
  else if byte = 0x37 then .brokerDealer
  else if byte = 0x38 then .marketMaker
  else if byte = 0x54 then .professionalCustomer
  else if byte = 0x57 then .brokerDealerClearedAsCustomer
  else .awayMarketMaker

def ofByte (byte : UInt8) : CounterpartAccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CounterpartAccountType) : ofByte value.toByte = value := by
  cases value with
  | publicCustomer => decide
  | brokerDealer => decide
  | marketMaker => decide
  | professionalCustomer => decide
  | brokerDealerClearedAsCustomer => decide
  | awayMarketMaker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CounterpartAccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CounterpartAccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CounterpartAccountType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CounterpartAccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CounterpartAccountType

/-- Quote Cancel Reason: one byte code -/
def QuoteCancelReason.codes : List UInt8 :=
  [0x41, 0x44, 0x45, 0x47, 0x49, 0x4C, 0x4D, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x4E, 0x56, 0x57]

inductive QuoteCancelReason where
  | cancelledByTheTrader -- Cancelled By The Trader
  | mmpPercentOfQuoteHasBeenReached -- Mmp Percent Of Quote Has Been Reached
  | maximumTriggersProtectionLimitExceeded -- Maximum Triggers Protection Limit Exceeded
  | cancelledBySupervisor -- Cancelled By Supervisor
  | eliminatedOnDisconnect -- Eliminated On Disconnect
  | tradedActivityProtectionLimitExceeded -- Traded Activity Protection Limit Exceeded
  | cancelledByTheBoxMarketOperationsCenterMoc -- Cancelled By The Box Market Operations Center Moc
  | eliminatedDueToDrillThroughProtection -- Eliminated Due To Drill Through Protection
  | mmpMaxNumberOfTradesHasBeenReached -- Mmp Max Number Of Trades Has Been Reached
  | quotesCancelled -- Quotes Cancelled
  | mmpMaxValueHasBeenReached -- Mmp Max Value Has Been Reached
  | cancelledByTheSystem -- Cancelled By The System
  | mmpMaxVolumeHasBeenReached -- Mmp Max Volume Has Been Reached
  | mmpMaxDeltaVolumeHasBeenReached -- Mmp Max Delta Volume Has Been Reached
  | mmpMaxDeltaValueHasBeenReached -- Mmp Max Delta Value Has Been Reached
  | cancelPending -- Cancel Pending
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCancelReason

def toByte : QuoteCancelReason → UInt8
  | .cancelledByTheTrader => 0x41
  | .mmpPercentOfQuoteHasBeenReached => 0x44
  | .maximumTriggersProtectionLimitExceeded => 0x45
  | .cancelledBySupervisor => 0x47
  | .eliminatedOnDisconnect => 0x49
  | .tradedActivityProtectionLimitExceeded => 0x4C
  | .cancelledByTheBoxMarketOperationsCenterMoc => 0x4D
  | .eliminatedDueToDrillThroughProtection => 0x4F
  | .mmpMaxNumberOfTradesHasBeenReached => 0x50
  | .quotesCancelled => 0x51
  | .mmpMaxValueHasBeenReached => 0x52
  | .cancelledByTheSystem => 0x53
  | .mmpMaxVolumeHasBeenReached => 0x54
  | .mmpMaxDeltaVolumeHasBeenReached => 0x4E
  | .mmpMaxDeltaValueHasBeenReached => 0x56
  | .cancelPending => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCancelReason :=
  if byte = 0x41 then .cancelledByTheTrader
  else if byte = 0x44 then .mmpPercentOfQuoteHasBeenReached
  else if byte = 0x45 then .maximumTriggersProtectionLimitExceeded
  else if byte = 0x47 then .cancelledBySupervisor
  else if byte = 0x49 then .eliminatedOnDisconnect
  else if byte = 0x4C then .tradedActivityProtectionLimitExceeded
  else if byte = 0x4D then .cancelledByTheBoxMarketOperationsCenterMoc
  else if byte = 0x4F then .eliminatedDueToDrillThroughProtection
  else if byte = 0x50 then .mmpMaxNumberOfTradesHasBeenReached
  else if byte = 0x51 then .quotesCancelled
  else if byte = 0x52 then .mmpMaxValueHasBeenReached
  else if byte = 0x53 then .cancelledByTheSystem
  else if byte = 0x54 then .mmpMaxVolumeHasBeenReached
  else if byte = 0x4E then .mmpMaxDeltaVolumeHasBeenReached
  else if byte = 0x56 then .mmpMaxDeltaValueHasBeenReached
  else .cancelPending

def ofByte (byte : UInt8) : QuoteCancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCancelReason) : ofByte value.toByte = value := by
  cases value with
  | cancelledByTheTrader => decide
  | mmpPercentOfQuoteHasBeenReached => decide
  | maximumTriggersProtectionLimitExceeded => decide
  | cancelledBySupervisor => decide
  | eliminatedOnDisconnect => decide
  | tradedActivityProtectionLimitExceeded => decide
  | cancelledByTheBoxMarketOperationsCenterMoc => decide
  | eliminatedDueToDrillThroughProtection => decide
  | mmpMaxNumberOfTradesHasBeenReached => decide
  | quotesCancelled => decide
  | mmpMaxValueHasBeenReached => decide
  | cancelledByTheSystem => decide
  | mmpMaxVolumeHasBeenReached => decide
  | mmpMaxDeltaVolumeHasBeenReached => decide
  | mmpMaxDeltaValueHasBeenReached => decide
  | cancelPending => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCancelReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCancelReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCancelReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteCancelReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCancelReason

/-- Verb: one byte code -/
def Verb.codes : List UInt8 :=
  [0x42, 0x53]

inductive Verb where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Verb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Verb

def toByte : Verb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Verb :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Verb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Verb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Verb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Verb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Verb) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Verb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Verb

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x4F, 0x51]

inductive OrderType where
  | order -- Order
  | quote -- Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .order => 0x4F
  | .quote => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x4F then .order
  else .quote

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | order => decide
  | quote => decide
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

/-- Action: one byte code -/
def Action.codes : List UInt8 :=
  [0x51, 0x53, 0x55]

inductive Action where
  | quantityUpdate -- Quantity Update
  | shelved -- Shelved
  | unshelved -- Unshelved
  | unlisted (byte : { byte : UInt8 // byte ∉ Action.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Action

def toByte : Action → UInt8
  | .quantityUpdate => 0x51
  | .shelved => 0x53
  | .unshelved => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Action :=
  if byte = 0x51 then .quantityUpdate
  else if byte = 0x53 then .shelved
  else .unshelved

def ofByte (byte : UInt8) : Action :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Action) : ofByte value.toByte = value := by
  cases value with
  | quantityUpdate => decide
  | shelved => decide
  | unshelved => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Action) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Action × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Action) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Action) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Action

/-- Heartbeat Question: 20 bytes -/
structure HeartbeatQuestion where
  userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod : Alpha 8
  lastExchangeMessageIdSentToParticipant : Alpha 6
  timeLocal : Alpha 6
  deriving DecidableEq, Repr

namespace HeartbeatQuestion

def encode (message : HeartbeatQuestion) : List UInt8 :=
  Alpha.encode message.userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod
    ++ (Alpha.encode message.lastExchangeMessageIdSentToParticipant
    ++ (Alpha.encode message.timeLocal))

def decode (bytes : List UInt8) : Option (HeartbeatQuestion × List UInt8) := do
  let (userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, bytes) ← Alpha.decode 8 bytes
  let (lastExchangeMessageIdSentToParticipant, bytes) ← Alpha.decode 6 bytes
  let (timeLocal, bytes) ← Alpha.decode 6 bytes
  pure ({ userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, lastExchangeMessageIdSentToParticipant, timeLocal }, bytes)

@[simp] theorem encode_length (message : HeartbeatQuestion) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatQuestion) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatQuestion) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatQuestion

/-- Out Of Sequence: 22 bytes -/
structure OutOfSequence where
  receivedUserSequenceId : Alpha 8
  expectedLastUserSequenceId : Alpha 8
  messageTimeLocal : Alpha 6
  deriving DecidableEq, Repr

namespace OutOfSequence

def encode (message : OutOfSequence) : List UInt8 :=
  Alpha.encode message.receivedUserSequenceId
    ++ (Alpha.encode message.expectedLastUserSequenceId
    ++ (Alpha.encode message.messageTimeLocal))

def decode (bytes : List UInt8) : Option (OutOfSequence × List UInt8) := do
  let (receivedUserSequenceId, bytes) ← Alpha.decode 8 bytes
  let (expectedLastUserSequenceId, bytes) ← Alpha.decode 8 bytes
  let (messageTimeLocal, bytes) ← Alpha.decode 6 bytes
  pure ({ receivedUserSequenceId, expectedLastUserSequenceId, messageTimeLocal }, bytes)

@[simp] theorem encode_length (message : OutOfSequence) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OutOfSequence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutOfSequence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutOfSequence

/-- Technical Error Notice: 218 bytes -/
structure TechnicalErrorNotice where
  receivedMessageType : Alpha 2
  precedingUserSequenceIdReceivedZeroesIfNone : Alpha 8
  errorCode : Alpha 4
  errorPosition : Alpha 4
  errorMessage : Alpha 100
  startOfMessageInError : Alpha 100
  deriving DecidableEq, Repr

namespace TechnicalErrorNotice

def encode (message : TechnicalErrorNotice) : List UInt8 :=
  Alpha.encode message.receivedMessageType
    ++ (Alpha.encode message.precedingUserSequenceIdReceivedZeroesIfNone
    ++ (Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorPosition
    ++ (Alpha.encode message.errorMessage
    ++ (Alpha.encode message.startOfMessageInError)))))

def decode (bytes : List UInt8) : Option (TechnicalErrorNotice × List UInt8) := do
  let (receivedMessageType, bytes) ← Alpha.decode 2 bytes
  let (precedingUserSequenceIdReceivedZeroesIfNone, bytes) ← Alpha.decode 8 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorPosition, bytes) ← Alpha.decode 4 bytes
  let (errorMessage, bytes) ← Alpha.decode 100 bytes
  let (startOfMessageInError, bytes) ← Alpha.decode 100 bytes
  pure ({ receivedMessageType, precedingUserSequenceIdReceivedZeroesIfNone, errorCode, errorPosition, errorMessage, startOfMessageInError }, bytes)

@[simp] theorem encode_length (message : TechnicalErrorNotice) : (encode message).length = 218 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TechnicalErrorNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TechnicalErrorNotice) (rest : List UInt8) :
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

end TechnicalErrorNotice

/-- Disconnection Instruction Acknowledgement: 12 bytes -/
structure DisconnectionInstructionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace DisconnectionInstructionAcknowledgement

def encode (message : DisconnectionInstructionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (DisconnectionInstructionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : DisconnectionInstructionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DisconnectionInstructionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionInstructionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DisconnectionInstructionAcknowledgement

/-- Connection Acknowledgement: 12 bytes -/
structure ConnectionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace ConnectionAcknowledgement

def encode (message : ConnectionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (ConnectionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : ConnectionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ConnectionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConnectionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ConnectionAcknowledgement

/-- Disconnection Acknowledgement: 12 bytes -/
structure DisconnectionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace DisconnectionAcknowledgement

def encode (message : DisconnectionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (DisconnectionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : DisconnectionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DisconnectionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DisconnectionAcknowledgement

/-- End Of Transmission: 18 bytes -/
structure EndOfTransmission where
  endedSessionId : Alpha 4
  lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes : Alpha 8
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmission

def encode (message : EndOfTransmission) : List UInt8 :=
  Alpha.encode message.endedSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes
    ++ (Alpha.encode message.time))

def decode (bytes : List UInt8) : Option (EndOfTransmission × List UInt8) := do
  let (endedSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes, bytes) ← Alpha.decode 8 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ endedSessionId, lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes, time }, bytes)

@[simp] theorem encode_length (message : EndOfTransmission) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmission) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmission) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmission

/-- Error Notice: 358 bytes -/
structure ErrorNotice where
  errorCode : Alpha 4
  errorDescription : Alpha 100
  group : Alpha 2
  instrument : Alpha 4
  orderIdClientOrderId20 : Alpha 20
  auctionId : Alpha 6
  originalMessageType : Alpha 2
  errorDetail : Alpha 200
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace ErrorNotice

def encode (message : ErrorNotice) : List UInt8 :=
  Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorDescription
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.orderIdClientOrderId20
    ++ (Alpha.encode message.auctionId
    ++ (Alpha.encode message.originalMessageType
    ++ (Alpha.encode message.errorDetail
    ++ (Alpha.encode message.clientOrderId))))))))

def decode (bytes : List UInt8) : Option (ErrorNotice × List UInt8) := do
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorDescription, bytes) ← Alpha.decode 100 bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (orderIdClientOrderId20, bytes) ← Alpha.decode 20 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (originalMessageType, bytes) ← Alpha.decode 2 bytes
  let (errorDetail, bytes) ← Alpha.decode 200 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ errorCode, errorDescription, group, instrument, orderIdClientOrderId20, auctionId, originalMessageType, errorDetail, clientOrderId }, bytes)

@[simp] theorem encode_length (message : ErrorNotice) : (encode message).length = 358 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ErrorNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorNotice) (rest : List UInt8) :
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

end ErrorNotice

/-- Bulk Quote Data Acknowledgement: 18 bytes -/
structure BulkQuoteDataAcknowledgement where
  group : Alpha 2
  traderId : Alpha 8
  quoteIdIdentifiesTradersQuoteOnThisGroup : Alpha 8
  deriving DecidableEq, Repr

namespace BulkQuoteDataAcknowledgement

def encode (message : BulkQuoteDataAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.quoteIdIdentifiesTradersQuoteOnThisGroup))

def decode (bytes : List UInt8) : Option (BulkQuoteDataAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (quoteIdIdentifiesTradersQuoteOnThisGroup, bytes) ← Alpha.decode 8 bytes
  pure ({ group, traderId, quoteIdIdentifiesTradersQuoteOnThisGroup }, bytes)

@[simp] theorem encode_length (message : BulkQuoteDataAcknowledgement) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BulkQuoteDataAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteDataAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteDataAcknowledgement

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

/-- Order Acknowledgement: 167 bytes -/
structure OrderAcknowledgement where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderIdOrderId8 : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  fillerNumeric66 : Alpha 6
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  deriving DecidableEq, Repr

namespace OrderAcknowledgement

def encode (message : OrderAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderIdOrderId8
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.fillerNumeric66
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44)))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (fillerNumeric66, bytes) ← Alpha.decode 6 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, orderIdOrderId8, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, fillerNumeric66, additionalClientMemo, fillerMustBeBlankString44 }, bytes)

@[simp] theorem encode_length (message : OrderAcknowledgement) : (encode message).length = 167 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAcknowledgement) (rest : List UInt8) :
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
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAcknowledgement

/-- Global Cancellation Confirmation: 11 bytes -/
structure GlobalCancellationConfirmation where
  group : Alpha 2
  traderId : Alpha 8
  typeOfCancellationOnlyQQuotesOnlyCanBeReturned : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned
  deriving DecidableEq, Repr

namespace GlobalCancellationConfirmation

def encode (message : GlobalCancellationConfirmation) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.traderId
    ++ (TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.encode message.typeOfCancellationOnlyQQuotesOnlyCanBeReturned))

def decode (bytes : List UInt8) : Option (GlobalCancellationConfirmation × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (typeOfCancellationOnlyQQuotesOnlyCanBeReturned, bytes) ← TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.decode bytes
  pure ({ group, traderId, typeOfCancellationOnlyQQuotesOnlyCanBeReturned }, bytes)

@[simp] theorem encode_length (message : GlobalCancellationConfirmation) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.encode_length]

theorem encode_length_pos (message : GlobalCancellationConfirmation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlobalCancellationConfirmation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.decode_encode, some_bind]
  rfl

end GlobalCancellationConfirmation

/-- Improvement Order Acknowlegment: 167 bytes -/
structure ImprovementOrderAcknowlegment where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderIdOrderId8 : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  auctionIdOnlyIfMessageTypeIsKiOrElseZeroes : Alpha 6
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  deriving DecidableEq, Repr

namespace ImprovementOrderAcknowlegment

def encode (message : ImprovementOrderAcknowlegment) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderIdOrderId8
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.auctionIdOnlyIfMessageTypeIsKiOrElseZeroes
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44)))))))))))))

def decode (bytes : List UInt8) : Option (ImprovementOrderAcknowlegment × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (auctionIdOnlyIfMessageTypeIsKiOrElseZeroes, bytes) ← Alpha.decode 6 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, orderIdOrderId8, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, auctionIdOnlyIfMessageTypeIsKiOrElseZeroes, additionalClientMemo, fillerMustBeBlankString44 }, bytes)

@[simp] theorem encode_length (message : ImprovementOrderAcknowlegment) : (encode message).length = 167 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : ImprovementOrderAcknowlegment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImprovementOrderAcknowlegment) (rest : List UInt8) :
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
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ImprovementOrderAcknowlegment

/-- Order Modification Acknowledgement: 167 bytes -/
structure OrderModificationAcknowledgement where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderIdOrderId8 : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  fillerNumeric66 : Alpha 6
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  deriving DecidableEq, Repr

namespace OrderModificationAcknowledgement

def encode (message : OrderModificationAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderIdOrderId8
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.fillerNumeric66
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44)))))))))))))

def decode (bytes : List UInt8) : Option (OrderModificationAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (fillerNumeric66, bytes) ← Alpha.decode 6 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, orderIdOrderId8, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, fillerNumeric66, additionalClientMemo, fillerMustBeBlankString44 }, bytes)

@[simp] theorem encode_length (message : OrderModificationAcknowledgement) : (encode message).length = 167 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderModificationAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModificationAcknowledgement) (rest : List UInt8) :
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
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModificationAcknowledgement

/-- New Complex Order Instrument Acknowledgement Occurrence: 16 bytes -/
structure NewComplexOrderInstrumentAcknowledgementOccurrence where
  legGroup : Alpha 2
  legInstrumentId : Alpha 4
  legVerb : LegVerb
  fillerMustBeSpaces : Alpha 1
  legQuantityRatio : Alpha 8
  deriving DecidableEq, Repr

namespace NewComplexOrderInstrumentAcknowledgementOccurrence

def encode (message : NewComplexOrderInstrumentAcknowledgementOccurrence) : List UInt8 :=
  Alpha.encode message.legGroup
    ++ (Alpha.encode message.legInstrumentId
    ++ (LegVerb.encode message.legVerb
    ++ (Alpha.encode message.fillerMustBeSpaces
    ++ (Alpha.encode message.legQuantityRatio))))

def decode (bytes : List UInt8) : Option (NewComplexOrderInstrumentAcknowledgementOccurrence × List UInt8) := do
  let (legGroup, bytes) ← Alpha.decode 2 bytes
  let (legInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (legVerb, bytes) ← LegVerb.decode bytes
  let (fillerMustBeSpaces, bytes) ← Alpha.decode 1 bytes
  let (legQuantityRatio, bytes) ← Alpha.decode 8 bytes
  pure ({ legGroup, legInstrumentId, legVerb, fillerMustBeSpaces, legQuantityRatio }, bytes)

@[simp] theorem encode_length (message : NewComplexOrderInstrumentAcknowledgementOccurrence) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LegVerb.encode_length]

theorem encode_length_pos (message : NewComplexOrderInstrumentAcknowledgementOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewComplexOrderInstrumentAcknowledgementOccurrence) (rest : List UInt8) :
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

end NewComplexOrderInstrumentAcknowledgementOccurrence

/-- New Complex Order Instrument Acknowledgement -/
structure NewComplexOrderInstrumentAcknowledgement where
  strategyGroup : Alpha 2
  strategyInstrumentId : Alpha 4
  creationStatus : Alpha 1
  newComplexOrderInstrumentAcknowledgementOccurrence : Digited 2 NewComplexOrderInstrumentAcknowledgementOccurrence
  deriving DecidableEq, Repr

namespace NewComplexOrderInstrumentAcknowledgement

def encode (message : NewComplexOrderInstrumentAcknowledgement) : List UInt8 :=
  Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrumentId
    ++ (Alpha.encode message.creationStatus
    ++ (encodeDigits 2 message.newComplexOrderInstrumentAcknowledgementOccurrence.val.length
    ++ (encodeMany NewComplexOrderInstrumentAcknowledgementOccurrence.encode message.newComplexOrderInstrumentAcknowledgementOccurrence.val))))

def decode (bytes : List UInt8) : Option (NewComplexOrderInstrumentAcknowledgement × List UInt8) := do
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (creationStatus, bytes) ← Alpha.decode 1 bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (newComplexOrderInstrumentAcknowledgementOccurrence_, bytes) ← decodeMany NewComplexOrderInstrumentAcknowledgementOccurrence.decode numberOfLegs bytes
  if fits_newComplexOrderInstrumentAcknowledgementOccurrence : newComplexOrderInstrumentAcknowledgementOccurrence_.length < 10 ^ 2 then
    pure ({ strategyGroup, strategyInstrumentId, creationStatus, newComplexOrderInstrumentAcknowledgementOccurrence := ⟨newComplexOrderInstrumentAcknowledgementOccurrence_, fits_newComplexOrderInstrumentAcknowledgementOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewComplexOrderInstrumentAcknowledgement) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewComplexOrderInstrumentAcknowledgement) : (encode message).length ≤ 1593 := by
  have bound_newComplexOrderInstrumentAcknowledgementOccurrence := message.newComplexOrderInstrumentAcknowledgementOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const NewComplexOrderInstrumentAcknowledgementOccurrence.encode 16 NewComplexOrderInstrumentAcknowledgementOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : NewComplexOrderInstrumentAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.newComplexOrderInstrumentAcknowledgementOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany NewComplexOrderInstrumentAcknowledgementOccurrence.encode NewComplexOrderInstrumentAcknowledgementOccurrence.decode NewComplexOrderInstrumentAcknowledgementOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newComplexOrderInstrumentAcknowledgementOccurrence.length_lt]
  rfl

end NewComplexOrderInstrumentAcknowledgement

/-- Standard Acknowledgement: 10 bytes -/
structure StandardAcknowledgement where
  traderId : Alpha 8
  originalMessageTypeReRfRqRpGz : Alpha 2
  deriving DecidableEq, Repr

namespace StandardAcknowledgement

def encode (message : StandardAcknowledgement) : List UInt8 :=
  Alpha.encode message.traderId
    ++ (Alpha.encode message.originalMessageTypeReRfRqRpGz)

def decode (bytes : List UInt8) : Option (StandardAcknowledgement × List UInt8) := do
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (originalMessageTypeReRfRqRpGz, bytes) ← Alpha.decode 2 bytes
  pure ({ traderId, originalMessageTypeReRfRqRpGz }, bytes)

@[simp] theorem encode_length (message : StandardAcknowledgement) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StandardAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StandardAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StandardAcknowledgement

/-- Complex Order Auction Acknowledgement: 167 bytes -/
structure ComplexOrderAuctionAcknowledgement where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderIdOrderId8 : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  auctionId : Alpha 6
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  deriving DecidableEq, Repr

namespace ComplexOrderAuctionAcknowledgement

def encode (message : ComplexOrderAuctionAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderIdOrderId8
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.auctionId
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44)))))))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderAuctionAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, orderIdOrderId8, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, auctionId, additionalClientMemo, fillerMustBeBlankString44 }, bytes)

@[simp] theorem encode_length (message : ComplexOrderAuctionAcknowledgement) : (encode message).length = 167 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : ComplexOrderAuctionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderAuctionAcknowledgement) (rest : List UInt8) :
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
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexOrderAuctionAcknowledgement

/-- Auction Or Improvement Cancellation Acknowledgement: 147 bytes -/
structure AuctionOrImprovementCancellationAcknowledgement where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderIdOrderId8 : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  auctionIdOnlyIfMessageTypeIsKiOrElseZeroes : Alpha 6
  deriving DecidableEq, Repr

namespace AuctionOrImprovementCancellationAcknowledgement

def encode (message : AuctionOrImprovementCancellationAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderIdOrderId8
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.auctionIdOnlyIfMessageTypeIsKiOrElseZeroes)))))))))))

def decode (bytes : List UInt8) : Option (AuctionOrImprovementCancellationAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (auctionIdOnlyIfMessageTypeIsKiOrElseZeroes, bytes) ← Alpha.decode 6 bytes
  pure ({ group, instrument, traderId, orderIdOrderId8, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, auctionIdOnlyIfMessageTypeIsKiOrElseZeroes }, bytes)

@[simp] theorem encode_length (message : AuctionOrImprovementCancellationAcknowledgement) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : AuctionOrImprovementCancellationAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionOrImprovementCancellationAcknowledgement) (rest : List UInt8) :
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
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end AuctionOrImprovementCancellationAcknowledgement

/-- Order Cancellation Acknowledgement: 167 bytes -/
structure OrderCancellationAcknowledgement where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderIdOrderId8 : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  auctionIdOnlyIfMessageTypeIsKiOrElseZeroes : Alpha 6
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  deriving DecidableEq, Repr

namespace OrderCancellationAcknowledgement

def encode (message : OrderCancellationAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderIdOrderId8
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.auctionIdOnlyIfMessageTypeIsKiOrElseZeroes
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44)))))))))))))

def decode (bytes : List UInt8) : Option (OrderCancellationAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (auctionIdOnlyIfMessageTypeIsKiOrElseZeroes, bytes) ← Alpha.decode 6 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, orderIdOrderId8, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, auctionIdOnlyIfMessageTypeIsKiOrElseZeroes, additionalClientMemo, fillerMustBeBlankString44 }, bytes)

@[simp] theorem encode_length (message : OrderCancellationAcknowledgement) : (encode message).length = 167 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderCancellationAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationAcknowledgement) (rest : List UInt8) :
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
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellationAcknowledgement

/-- Bulk Quote Acknowledgement Occurrence: 7 bytes -/
structure BulkQuoteAcknowledgementOccurrence where
  quoteNumber : Alpha 3
  errorCode : Alpha 4
  deriving DecidableEq, Repr

namespace BulkQuoteAcknowledgementOccurrence

def encode (message : BulkQuoteAcknowledgementOccurrence) : List UInt8 :=
  Alpha.encode message.quoteNumber
    ++ (Alpha.encode message.errorCode)

def decode (bytes : List UInt8) : Option (BulkQuoteAcknowledgementOccurrence × List UInt8) := do
  let (quoteNumber, bytes) ← Alpha.decode 3 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  pure ({ quoteNumber, errorCode }, bytes)

@[simp] theorem encode_length (message : BulkQuoteAcknowledgementOccurrence) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BulkQuoteAcknowledgementOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteAcknowledgementOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteAcknowledgementOccurrence

/-- Bulk Quote Acknowledgement -/
structure BulkQuoteAcknowledgement where
  group : Alpha 2
  quoteIdIdentifiesTradersQuoteOnThisGroup : Alpha 8
  bulkQuoteAcknowledgementOccurrence : Digited 3 BulkQuoteAcknowledgementOccurrence
  deriving DecidableEq, Repr

namespace BulkQuoteAcknowledgement

def encode (message : BulkQuoteAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdIdentifiesTradersQuoteOnThisGroup
    ++ (encodeDigits 3 message.bulkQuoteAcknowledgementOccurrence.val.length
    ++ (encodeMany BulkQuoteAcknowledgementOccurrence.encode message.bulkQuoteAcknowledgementOccurrence.val)))

def decode (bytes : List UInt8) : Option (BulkQuoteAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdIdentifiesTradersQuoteOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotesInError, bytes) ← decodeDigits 3 bytes
  let (bulkQuoteAcknowledgementOccurrence_, bytes) ← decodeMany BulkQuoteAcknowledgementOccurrence.decode numberOfQuotesInError bytes
  if fits_bulkQuoteAcknowledgementOccurrence : bulkQuoteAcknowledgementOccurrence_.length < 10 ^ 3 then
    pure ({ group, quoteIdIdentifiesTradersQuoteOnThisGroup, bulkQuoteAcknowledgementOccurrence := ⟨bulkQuoteAcknowledgementOccurrence_, fits_bulkQuoteAcknowledgementOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuoteAcknowledgement) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuoteAcknowledgement) : (encode message).length ≤ 7006 := by
  have bound_bulkQuoteAcknowledgementOccurrence := message.bulkQuoteAcknowledgementOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuoteAcknowledgementOccurrence.encode 7 BulkQuoteAcknowledgementOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuoteAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuoteAcknowledgementOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuoteAcknowledgementOccurrence.encode BulkQuoteAcknowledgementOccurrence.decode BulkQuoteAcknowledgementOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuoteAcknowledgementOccurrence.length_lt]
  rfl

end BulkQuoteAcknowledgement

/-- Trader Status: 10 bytes -/
structure TraderStatus where
  traderId : Alpha 8
  traderLockOut : TraderLockOut
  riskTeamLockOut : RiskTeamLockOut
  deriving DecidableEq, Repr

namespace TraderStatus

def encode (message : TraderStatus) : List UInt8 :=
  Alpha.encode message.traderId
    ++ (TraderLockOut.encode message.traderLockOut
    ++ (RiskTeamLockOut.encode message.riskTeamLockOut))

def decode (bytes : List UInt8) : Option (TraderStatus × List UInt8) := do
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (traderLockOut, bytes) ← TraderLockOut.decode bytes
  let (riskTeamLockOut, bytes) ← RiskTeamLockOut.decode bytes
  pure ({ traderId, traderLockOut, riskTeamLockOut }, bytes)

@[simp] theorem encode_length (message : TraderStatus) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TraderLockOut.encode_length, RiskTeamLockOut.encode_length]

theorem encode_length_pos (message : TraderStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TraderStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TraderLockOut.decode_encode, some_bind]
  dsimp only
  rw [RiskTeamLockOut.decode_encode, some_bind]
  rfl

end TraderStatus

/-- Directed Order Cancellation Notice: 41 bytes -/
structure DirectedOrderCancellationNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  verbSide : VerbSide
  quantity : Alpha 8
  price : Alpha 10
  referencedOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace DirectedOrderCancellationNotice

def encode (message : DirectedOrderCancellationNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.referencedOrderId))))))

def decode (bytes : List UInt8) : Option (DirectedOrderCancellationNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (referencedOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, traderId, verbSide, quantity, price, referencedOrderId }, bytes)

@[simp] theorem encode_length (message : DirectedOrderCancellationNotice) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length]

theorem encode_length_pos (message : DirectedOrderCancellationNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DirectedOrderCancellationNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DirectedOrderCancellationNotice

/-- Directed Order Notice: 41 bytes -/
structure DirectedOrderNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  verbSide : VerbSide
  quantity : Alpha 8
  price : Alpha 10
  referencedOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace DirectedOrderNotice

def encode (message : DirectedOrderNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.referencedOrderId))))))

def decode (bytes : List UInt8) : Option (DirectedOrderNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (referencedOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, traderId, verbSide, quantity, price, referencedOrderId }, bytes)

@[simp] theorem encode_length (message : DirectedOrderNotice) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length]

theorem encode_length_pos (message : DirectedOrderNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DirectedOrderNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DirectedOrderNotice

/-- Excluded Instrument Notice: 22 bytes -/
structure ExcludedInstrumentNotice where
  group : Alpha 2
  fillerString22 : Alpha 2
  traderId : Alpha 8
  filler2 : Alpha 2
  nbOfInstruments : Alpha 4
  t1To9999OccurrencesInstrument : Alpha 4
  deriving DecidableEq, Repr

namespace ExcludedInstrumentNotice

def encode (message : ExcludedInstrumentNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.fillerString22
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.nbOfInstruments
    ++ (Alpha.encode message.t1To9999OccurrencesInstrument)))))

def decode (bytes : List UInt8) : Option (ExcludedInstrumentNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (fillerString22, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (nbOfInstruments, bytes) ← Alpha.decode 4 bytes
  let (t1To9999OccurrencesInstrument, bytes) ← Alpha.decode 4 bytes
  pure ({ group, fillerString22, traderId, filler2, nbOfInstruments, t1To9999OccurrencesInstrument }, bytes)

@[simp] theorem encode_length (message : ExcludedInstrumentNotice) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ExcludedInstrumentNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExcludedInstrumentNotice) (rest : List UInt8) :
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

end ExcludedInstrumentNotice

/-- Group State Change: 3 bytes -/
structure GroupStateChange where
  group : Alpha 2
  groupState : GroupState
  deriving DecidableEq, Repr

namespace GroupStateChange

def encode (message : GroupStateChange) : List UInt8 :=
  Alpha.encode message.group
    ++ (GroupState.encode message.groupState)

def decode (bytes : List UInt8) : Option (GroupStateChange × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (groupState, bytes) ← GroupState.decode bytes
  pure ({ group, groupState }, bytes)

@[simp] theorem encode_length (message : GroupStateChange) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, GroupState.encode_length]

theorem encode_length_pos (message : GroupStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GroupState.decode_encode, some_bind]
  rfl

end GroupStateChange

/-- Leg Execution Notice: 257 bytes -/
structure LegExecutionNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceId : Alpha 8
  verbSide : VerbSide
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  timeTradeHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : SpecialTradeIndicator
  priceType : PriceType
  tradeType : TradeType
  auctionId : Alpha 6
  tradeNumber : Alpha 8
  tradeMemoString5050 : Alpha 50
  originalReferenceIdOrderId8 : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  liquidityStatus : LiquidityStatus
  strategyGroup : Alpha 2
  strategyInstrumentId : Alpha 4
  strategyVerbSide : StrategyVerbSide
  strategyTradeNumber : Alpha 8
  legNumber : Alpha 2
  counterpartAccountType : CounterpartAccountType
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString11 : Alpha 1
  fillerZeroFilled : Alpha 4
  deriving DecidableEq, Repr

namespace LegExecutionNotice

def encode (message : LegExecutionNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.timeTradeHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (SpecialTradeIndicator.encode message.specialTradeIndicator
    ++ (PriceType.encode message.priceType
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.auctionId
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemoString5050
    ++ (Alpha.encode message.originalReferenceIdOrderId8
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrumentId
    ++ (StrategyVerbSide.encode message.strategyVerbSide
    ++ (Alpha.encode message.strategyTradeNumber
    ++ (Alpha.encode message.legNumber
    ++ (CounterpartAccountType.encode message.counterpartAccountType
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString11
    ++ (Alpha.encode message.fillerZeroFilled)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (LegExecutionNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (timeTradeHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← SpecialTradeIndicator.decode bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemoString5050, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (strategyVerbSide, bytes) ← StrategyVerbSide.decode bytes
  let (strategyTradeNumber, bytes) ← Alpha.decode 8 bytes
  let (legNumber, bytes) ← Alpha.decode 2 bytes
  let (counterpartAccountType, bytes) ← CounterpartAccountType.decode bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString11, bytes) ← Alpha.decode 1 bytes
  let (fillerZeroFilled, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, referenceId, verbSide, quantityTraded, tradePrice, timeTradeHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, auctionId, tradeNumber, tradeMemoString5050, originalReferenceIdOrderId8, idCodeForTheCounterpartParticipant, liquidityStatus, strategyGroup, strategyInstrumentId, strategyVerbSide, strategyTradeNumber, legNumber, counterpartAccountType, additionalClientMemo, fillerMustBeBlankString11, fillerZeroFilled }, bytes)

@[simp] theorem encode_length (message : LegExecutionNotice) : (encode message).length = 257 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length, SpecialTradeIndicator.encode_length, PriceType.encode_length, TradeType.encode_length, LiquidityStatus.encode_length, StrategyVerbSide.encode_length, CounterpartAccountType.encode_length]

theorem encode_length_pos (message : LegExecutionNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : LegExecutionNotice) (rest : List UInt8) :
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
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, SpecialTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyVerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CounterpartAccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegExecutionNotice

/-- Cancellation Of All Quotes Notices: 15 bytes -/
structure CancellationOfAllQuotesNotices where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  quoteCancelReason : QuoteCancelReason
  deriving DecidableEq, Repr

namespace CancellationOfAllQuotesNotices

def encode (message : CancellationOfAllQuotesNotices) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (QuoteCancelReason.encode message.quoteCancelReason)))

def decode (bytes : List UInt8) : Option (CancellationOfAllQuotesNotices × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (quoteCancelReason, bytes) ← QuoteCancelReason.decode bytes
  pure ({ group, instrument, traderId, quoteCancelReason }, bytes)

@[simp] theorem encode_length (message : CancellationOfAllQuotesNotices) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, QuoteCancelReason.encode_length]

theorem encode_length_pos (message : CancellationOfAllQuotesNotices) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancellationOfAllQuotesNotices) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [QuoteCancelReason.decode_encode, some_bind]
  rfl

end CancellationOfAllQuotesNotices

/-- Quality Market Maker Notification: 65 bytes -/
structure QualityMarketMakerNotification where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  auctionId : Alpha 6
  verb : Verb
  auctionQuantity : Alpha 8
  auctionPrice : Alpha 10
  quoteQuantity : Alpha 8
  quotePrice : Alpha 10
  qualifiedQuantity : Alpha 8
  deriving DecidableEq, Repr

namespace QualityMarketMakerNotification

def encode (message : QualityMarketMakerNotification) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.auctionId
    ++ (Verb.encode message.verb
    ++ (Alpha.encode message.auctionQuantity
    ++ (Alpha.encode message.auctionPrice
    ++ (Alpha.encode message.quoteQuantity
    ++ (Alpha.encode message.quotePrice
    ++ (Alpha.encode message.qualifiedQuantity)))))))))

def decode (bytes : List UInt8) : Option (QualityMarketMakerNotification × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (verb, bytes) ← Verb.decode bytes
  let (auctionQuantity, bytes) ← Alpha.decode 8 bytes
  let (auctionPrice, bytes) ← Alpha.decode 10 bytes
  let (quoteQuantity, bytes) ← Alpha.decode 8 bytes
  let (quotePrice, bytes) ← Alpha.decode 10 bytes
  let (qualifiedQuantity, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, traderId, auctionId, verb, auctionQuantity, auctionPrice, quoteQuantity, quotePrice, qualifiedQuantity }, bytes)

@[simp] theorem encode_length (message : QualityMarketMakerNotification) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Verb.encode_length]

theorem encode_length_pos (message : QualityMarketMakerNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QualityMarketMakerNotification) (rest : List UInt8) :
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
  rw [List.append_assoc, Verb.decode_encode, some_bind]
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

end QualityMarketMakerNotification

/-- Execution Notice: 240 bytes -/
structure ExecutionNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : VerbSide
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  timeOfTheTradeHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : SpecialTradeIndicator
  priceType : PriceType
  tradeType : TradeType
  auctionId : Alpha 6
  tradeNumber : Alpha 8
  tradeMemoTradeMemo50 : Alpha 50
  originalReferenceIdOriginalReferenceId8 : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  liquidityStatus : LiquidityStatus
  counterpartAccountType : CounterpartAccountType
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString11 : Alpha 1
  fillerZeroFilled : Alpha 4
  deriving DecidableEq, Repr

namespace ExecutionNotice

def encode (message : ExecutionNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.timeOfTheTradeHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (SpecialTradeIndicator.encode message.specialTradeIndicator
    ++ (PriceType.encode message.priceType
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.auctionId
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemoTradeMemo50
    ++ (Alpha.encode message.originalReferenceIdOriginalReferenceId8
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (CounterpartAccountType.encode message.counterpartAccountType
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString11
    ++ (Alpha.encode message.fillerZeroFilled))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (timeOfTheTradeHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← SpecialTradeIndicator.decode bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemoTradeMemo50, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceIdOriginalReferenceId8, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (counterpartAccountType, bytes) ← CounterpartAccountType.decode bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString11, bytes) ← Alpha.decode 1 bytes
  let (fillerZeroFilled, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, timeOfTheTradeHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, auctionId, tradeNumber, tradeMemoTradeMemo50, originalReferenceIdOriginalReferenceId8, idCodeForTheCounterpartParticipant, liquidityStatus, counterpartAccountType, additionalClientMemo, fillerMustBeBlankString11, fillerZeroFilled }, bytes)

@[simp] theorem encode_length (message : ExecutionNotice) : (encode message).length = 240 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length, SpecialTradeIndicator.encode_length, PriceType.encode_length, TradeType.encode_length, LiquidityStatus.encode_length, CounterpartAccountType.encode_length]

theorem encode_length_pos (message : ExecutionNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionNotice) (rest : List UInt8) :
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
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, SpecialTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CounterpartAccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutionNotice

/-- Quote Notice: 75 bytes -/
structure QuoteNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdQuote : Alpha 8
  verbSide : VerbSide
  orderType : OrderType
  action : Action
  newQuantity : Alpha 8
  newPrice : Alpha 10
  previousQuantity : Alpha 8
  previousPrice : Alpha 10
  auctionId : Alpha 6
  originalReferenceIdQuoteOrOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace QuoteNotice

def encode (message : QuoteNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdQuote
    ++ (VerbSide.encode message.verbSide
    ++ (OrderType.encode message.orderType
    ++ (Action.encode message.action
    ++ (Alpha.encode message.newQuantity
    ++ (Alpha.encode message.newPrice
    ++ (Alpha.encode message.previousQuantity
    ++ (Alpha.encode message.previousPrice
    ++ (Alpha.encode message.auctionId
    ++ (Alpha.encode message.originalReferenceIdQuoteOrOrderId))))))))))))

def decode (bytes : List UInt8) : Option (QuoteNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdQuote, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (action, bytes) ← Action.decode bytes
  let (newQuantity, bytes) ← Alpha.decode 8 bytes
  let (newPrice, bytes) ← Alpha.decode 10 bytes
  let (previousQuantity, bytes) ← Alpha.decode 8 bytes
  let (previousPrice, bytes) ← Alpha.decode 10 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (originalReferenceIdQuoteOrOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, traderId, referenceIdQuote, verbSide, orderType, action, newQuantity, newPrice, previousQuantity, previousPrice, auctionId, originalReferenceIdQuoteOrOrderId }, bytes)

@[simp] theorem encode_length (message : QuoteNotice) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, OrderType.encode_length, Action.encode_length]

theorem encode_length_pos (message : QuoteNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteNotice) (rest : List UInt8) :
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
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
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

end QuoteNotice

/-- Execution Cancellation Notice: 240 bytes -/
structure ExecutionCancellationNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : VerbSide
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  timeOfTheTradeHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : SpecialTradeIndicator
  priceType : PriceType
  tradeType : TradeType
  auctionId : Alpha 6
  tradeNumber : Alpha 8
  tradeMemoTradeMemo50 : Alpha 50
  originalReferenceIdOriginalReferenceId8 : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  liquidityStatus : LiquidityStatus
  counterpartAccountType : CounterpartAccountType
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString11 : Alpha 1
  fillerZeroFilled : Alpha 4
  deriving DecidableEq, Repr

namespace ExecutionCancellationNotice

def encode (message : ExecutionCancellationNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.timeOfTheTradeHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (SpecialTradeIndicator.encode message.specialTradeIndicator
    ++ (PriceType.encode message.priceType
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.auctionId
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemoTradeMemo50
    ++ (Alpha.encode message.originalReferenceIdOriginalReferenceId8
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (CounterpartAccountType.encode message.counterpartAccountType
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString11
    ++ (Alpha.encode message.fillerZeroFilled))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionCancellationNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (timeOfTheTradeHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← SpecialTradeIndicator.decode bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemoTradeMemo50, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceIdOriginalReferenceId8, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (counterpartAccountType, bytes) ← CounterpartAccountType.decode bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString11, bytes) ← Alpha.decode 1 bytes
  let (fillerZeroFilled, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, timeOfTheTradeHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, auctionId, tradeNumber, tradeMemoTradeMemo50, originalReferenceIdOriginalReferenceId8, idCodeForTheCounterpartParticipant, liquidityStatus, counterpartAccountType, additionalClientMemo, fillerMustBeBlankString11, fillerZeroFilled }, bytes)

@[simp] theorem encode_length (message : ExecutionCancellationNotice) : (encode message).length = 240 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length, SpecialTradeIndicator.encode_length, PriceType.encode_length, TradeType.encode_length, LiquidityStatus.encode_length, CounterpartAccountType.encode_length]

theorem encode_length_pos (message : ExecutionCancellationNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionCancellationNotice) (rest : List UInt8) :
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
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, SpecialTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CounterpartAccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutionCancellationNotice

/-- Leg Execution Cancellation Notice: 257 bytes -/
structure LegExecutionCancellationNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceId : Alpha 8
  verbSide : VerbSide
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  timeTradeHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : SpecialTradeIndicator
  priceType : PriceType
  tradeType : TradeType
  auctionId : Alpha 6
  tradeNumber : Alpha 8
  tradeMemoString5050 : Alpha 50
  originalReferenceIdOrderId8 : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  liquidityStatus : LiquidityStatus
  strategyGroup : Alpha 2
  strategyInstrumentId : Alpha 4
  strategyVerbSide : StrategyVerbSide
  strategyTradeNumber : Alpha 8
  legNumber : Alpha 2
  counterpartAccountType : CounterpartAccountType
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString11 : Alpha 1
  fillerZeroFilled : Alpha 4
  deriving DecidableEq, Repr

namespace LegExecutionCancellationNotice

def encode (message : LegExecutionCancellationNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.timeTradeHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (SpecialTradeIndicator.encode message.specialTradeIndicator
    ++ (PriceType.encode message.priceType
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.auctionId
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemoString5050
    ++ (Alpha.encode message.originalReferenceIdOrderId8
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrumentId
    ++ (StrategyVerbSide.encode message.strategyVerbSide
    ++ (Alpha.encode message.strategyTradeNumber
    ++ (Alpha.encode message.legNumber
    ++ (CounterpartAccountType.encode message.counterpartAccountType
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString11
    ++ (Alpha.encode message.fillerZeroFilled)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (LegExecutionCancellationNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (timeTradeHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← SpecialTradeIndicator.decode bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemoString5050, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (strategyVerbSide, bytes) ← StrategyVerbSide.decode bytes
  let (strategyTradeNumber, bytes) ← Alpha.decode 8 bytes
  let (legNumber, bytes) ← Alpha.decode 2 bytes
  let (counterpartAccountType, bytes) ← CounterpartAccountType.decode bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString11, bytes) ← Alpha.decode 1 bytes
  let (fillerZeroFilled, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, referenceId, verbSide, quantityTraded, tradePrice, timeTradeHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, auctionId, tradeNumber, tradeMemoString5050, originalReferenceIdOrderId8, idCodeForTheCounterpartParticipant, liquidityStatus, strategyGroup, strategyInstrumentId, strategyVerbSide, strategyTradeNumber, legNumber, counterpartAccountType, additionalClientMemo, fillerMustBeBlankString11, fillerZeroFilled }, bytes)

@[simp] theorem encode_length (message : LegExecutionCancellationNotice) : (encode message).length = 257 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length, SpecialTradeIndicator.encode_length, PriceType.encode_length, TradeType.encode_length, LiquidityStatus.encode_length, StrategyVerbSide.encode_length, CounterpartAccountType.encode_length]

theorem encode_length_pos (message : LegExecutionCancellationNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : LegExecutionCancellationNotice) (rest : List UInt8) :
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
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, SpecialTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyVerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CounterpartAccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegExecutionCancellationNotice

/-- Order Cancellation Notice By System: 167 bytes -/
structure OrderCancellationNoticeBySystem where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderIdOrderId8 : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  auctionIdOnlyIfMessageTypeIsKiOrElseZeroes : Alpha 6
  additionalClientMemo : Alpha 16
  fillerMustBeBlankString44 : Alpha 4
  deriving DecidableEq, Repr

namespace OrderCancellationNoticeBySystem

def encode (message : OrderCancellationNoticeBySystem) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderIdOrderId8
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.auctionIdOnlyIfMessageTypeIsKiOrElseZeroes
    ++ (Alpha.encode message.additionalClientMemo
    ++ (Alpha.encode message.fillerMustBeBlankString44)))))))))))))

def decode (bytes : List UInt8) : Option (OrderCancellationNoticeBySystem × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderIdOrderId8, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (auctionIdOnlyIfMessageTypeIsKiOrElseZeroes, bytes) ← Alpha.decode 6 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  let (fillerMustBeBlankString44, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, orderIdOrderId8, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, auctionIdOnlyIfMessageTypeIsKiOrElseZeroes, additionalClientMemo, fillerMustBeBlankString44 }, bytes)

@[simp] theorem encode_length (message : OrderCancellationNoticeBySystem) : (encode message).length = 167 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderCancellationNoticeBySystem) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationNoticeBySystem) (rest : List UInt8) :
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
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellationNoticeBySystem

/-- Any Exchange Message, selected by Message Type -/
inductive ExchangeMessage where
  | heartbeatQuestion (message : HeartbeatQuestion) -- "TH" 0x5448
  | outOfSequence (message : OutOfSequence) -- "TO" 0x544F
  | technicalErrorNotice (message : TechnicalErrorNotice) -- "TE" 0x5445
  | disconnectionInstructionAcknowledgement (message : DisconnectionInstructionAcknowledgement) -- "TM" 0x544D
  | connectionAcknowledgement (message : ConnectionAcknowledgement) -- "TK" 0x544B
  | disconnectionAcknowledgement (message : DisconnectionAcknowledgement) -- "TL" 0x544C
  | endOfTransmission (message : EndOfTransmission) -- "TT" 0x5454
  | errorNotice (message : ErrorNotice) -- "ER" 0x4552
  | bulkQuoteDataAcknowledgement (message : BulkQuoteDataAcknowledgement) -- "KD" 0x4B44
  | orderAcknowledgement (message : OrderAcknowledgement) -- "KE" 0x4B45
  | globalCancellationConfirmation (message : GlobalCancellationConfirmation) -- "KG" 0x4B47
  | improvementOrderAcknowlegment (message : ImprovementOrderAcknowlegment) -- "KI" 0x4B49
  | orderModificationAcknowledgement (message : OrderModificationAcknowledgement) -- "KM" 0x4B4D
  | newComplexOrderInstrumentAcknowledgement (message : NewComplexOrderInstrumentAcknowledgement) -- "KN" 0x4B4E
  | standardAcknowledgement (message : StandardAcknowledgement) -- "KO" 0x4B4F
  | complexOrderAuctionAcknowledgement (message : ComplexOrderAuctionAcknowledgement) -- "KT" 0x4B54
  | auctionOrImprovementCancellationAcknowledgement (message : AuctionOrImprovementCancellationAcknowledgement) -- "KY" 0x4B59
  | orderCancellationAcknowledgement (message : OrderCancellationAcknowledgement) -- "KZ" 0x4B5A
  | bulkQuoteAcknowledgement (message : BulkQuoteAcknowledgement) -- "LA" 0x4C41
  | traderStatus (message : TraderStatus) -- "MU" 0x4D55
  | directedOrderCancellationNotice (message : DirectedOrderCancellationNotice) -- "NC" 0x4E43
  | directedOrderNotice (message : DirectedOrderNotice) -- "ND" 0x4E44
  | excludedInstrumentNotice (message : ExcludedInstrumentNotice) -- "NE" 0x4E45
  | groupStateChange (message : GroupStateChange) -- "NG" 0x4E47
  | legExecutionNotice (message : LegExecutionNotice) -- "NL" 0x4E4C
  | cancellationOfAllQuotesNotices (message : CancellationOfAllQuotesNotices) -- "NP" 0x4E50
  | qualityMarketMakerNotification (message : QualityMarketMakerNotification) -- "NQ" 0x4E51
  | executionNotice (message : ExecutionNotice) -- "NT" 0x4E54
  | quoteNotice (message : QuoteNotice) -- "NU" 0x4E55
  | executionCancellationNotice (message : ExecutionCancellationNotice) -- "NX" 0x4E58
  | legExecutionCancellationNotice (message : LegExecutionCancellationNotice) -- "NY" 0x4E59
  | orderCancellationNoticeBySystem (message : OrderCancellationNoticeBySystem) -- "NZ" 0x4E5A
  deriving DecidableEq, Repr

namespace ExchangeMessage

/-- The Message Type each message is sent under -/
def tag : ExchangeMessage → BitVec 16
  | .heartbeatQuestion _ => 21576
  | .outOfSequence _ => 21583
  | .technicalErrorNotice _ => 21573
  | .disconnectionInstructionAcknowledgement _ => 21581
  | .connectionAcknowledgement _ => 21579
  | .disconnectionAcknowledgement _ => 21580
  | .endOfTransmission _ => 21588
  | .errorNotice _ => 17746
  | .bulkQuoteDataAcknowledgement _ => 19268
  | .orderAcknowledgement _ => 19269
  | .globalCancellationConfirmation _ => 19271
  | .improvementOrderAcknowlegment _ => 19273
  | .orderModificationAcknowledgement _ => 19277
  | .newComplexOrderInstrumentAcknowledgement _ => 19278
  | .standardAcknowledgement _ => 19279
  | .complexOrderAuctionAcknowledgement _ => 19284
  | .auctionOrImprovementCancellationAcknowledgement _ => 19289
  | .orderCancellationAcknowledgement _ => 19290
  | .bulkQuoteAcknowledgement _ => 19521
  | .traderStatus _ => 19797
  | .directedOrderCancellationNotice _ => 20035
  | .directedOrderNotice _ => 20036
  | .excludedInstrumentNotice _ => 20037
  | .groupStateChange _ => 20039
  | .legExecutionNotice _ => 20044
  | .cancellationOfAllQuotesNotices _ => 20048
  | .qualityMarketMakerNotification _ => 20049
  | .executionNotice _ => 20052
  | .quoteNotice _ => 20053
  | .executionCancellationNotice _ => 20056
  | .legExecutionCancellationNotice _ => 20057
  | .orderCancellationNoticeBySystem _ => 20058

def encode : ExchangeMessage → List UInt8
  | .heartbeatQuestion message => HeartbeatQuestion.encode message
  | .outOfSequence message => OutOfSequence.encode message
  | .technicalErrorNotice message => TechnicalErrorNotice.encode message
  | .disconnectionInstructionAcknowledgement message => DisconnectionInstructionAcknowledgement.encode message
  | .connectionAcknowledgement message => ConnectionAcknowledgement.encode message
  | .disconnectionAcknowledgement message => DisconnectionAcknowledgement.encode message
  | .endOfTransmission message => EndOfTransmission.encode message
  | .errorNotice message => ErrorNotice.encode message
  | .bulkQuoteDataAcknowledgement message => BulkQuoteDataAcknowledgement.encode message
  | .orderAcknowledgement message => OrderAcknowledgement.encode message
  | .globalCancellationConfirmation message => GlobalCancellationConfirmation.encode message
  | .improvementOrderAcknowlegment message => ImprovementOrderAcknowlegment.encode message
  | .orderModificationAcknowledgement message => OrderModificationAcknowledgement.encode message
  | .newComplexOrderInstrumentAcknowledgement message => NewComplexOrderInstrumentAcknowledgement.encode message
  | .standardAcknowledgement message => StandardAcknowledgement.encode message
  | .complexOrderAuctionAcknowledgement message => ComplexOrderAuctionAcknowledgement.encode message
  | .auctionOrImprovementCancellationAcknowledgement message => AuctionOrImprovementCancellationAcknowledgement.encode message
  | .orderCancellationAcknowledgement message => OrderCancellationAcknowledgement.encode message
  | .bulkQuoteAcknowledgement message => BulkQuoteAcknowledgement.encode message
  | .traderStatus message => TraderStatus.encode message
  | .directedOrderCancellationNotice message => DirectedOrderCancellationNotice.encode message
  | .directedOrderNotice message => DirectedOrderNotice.encode message
  | .excludedInstrumentNotice message => ExcludedInstrumentNotice.encode message
  | .groupStateChange message => GroupStateChange.encode message
  | .legExecutionNotice message => LegExecutionNotice.encode message
  | .cancellationOfAllQuotesNotices message => CancellationOfAllQuotesNotices.encode message
  | .qualityMarketMakerNotification message => QualityMarketMakerNotification.encode message
  | .executionNotice message => ExecutionNotice.encode message
  | .quoteNotice message => QuoteNotice.encode message
  | .executionCancellationNotice message => ExecutionCancellationNotice.encode message
  | .legExecutionCancellationNotice message => LegExecutionCancellationNotice.encode message
  | .orderCancellationNoticeBySystem message => OrderCancellationNoticeBySystem.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ExchangeMessage) : (encode message).length ≤ 7006 := by
  cases message with
  | heartbeatQuestion inner =>
    simp only [encode, HeartbeatQuestion.encode_length]
    omega
  | outOfSequence inner =>
    simp only [encode, OutOfSequence.encode_length]
    omega
  | technicalErrorNotice inner =>
    simp only [encode, TechnicalErrorNotice.encode_length]
    omega
  | disconnectionInstructionAcknowledgement inner =>
    simp only [encode, DisconnectionInstructionAcknowledgement.encode_length]
    omega
  | connectionAcknowledgement inner =>
    simp only [encode, ConnectionAcknowledgement.encode_length]
    omega
  | disconnectionAcknowledgement inner =>
    simp only [encode, DisconnectionAcknowledgement.encode_length]
    omega
  | endOfTransmission inner =>
    simp only [encode, EndOfTransmission.encode_length]
    omega
  | errorNotice inner =>
    simp only [encode, ErrorNotice.encode_length]
    omega
  | bulkQuoteDataAcknowledgement inner =>
    simp only [encode, BulkQuoteDataAcknowledgement.encode_length]
    omega
  | orderAcknowledgement inner =>
    simp only [encode, OrderAcknowledgement.encode_length]
    omega
  | globalCancellationConfirmation inner =>
    simp only [encode, GlobalCancellationConfirmation.encode_length]
    omega
  | improvementOrderAcknowlegment inner =>
    simp only [encode, ImprovementOrderAcknowlegment.encode_length]
    omega
  | orderModificationAcknowledgement inner =>
    simp only [encode, OrderModificationAcknowledgement.encode_length]
    omega
  | newComplexOrderInstrumentAcknowledgement inner =>
    have bound_inner := NewComplexOrderInstrumentAcknowledgement.encode_length_le inner
    simp only [encode]
    omega
  | standardAcknowledgement inner =>
    simp only [encode, StandardAcknowledgement.encode_length]
    omega
  | complexOrderAuctionAcknowledgement inner =>
    simp only [encode, ComplexOrderAuctionAcknowledgement.encode_length]
    omega
  | auctionOrImprovementCancellationAcknowledgement inner =>
    simp only [encode, AuctionOrImprovementCancellationAcknowledgement.encode_length]
    omega
  | orderCancellationAcknowledgement inner =>
    simp only [encode, OrderCancellationAcknowledgement.encode_length]
    omega
  | bulkQuoteAcknowledgement inner =>
    have bound_inner := BulkQuoteAcknowledgement.encode_length_le inner
    simp only [encode]
    omega
  | traderStatus inner =>
    simp only [encode, TraderStatus.encode_length]
    omega
  | directedOrderCancellationNotice inner =>
    simp only [encode, DirectedOrderCancellationNotice.encode_length]
    omega
  | directedOrderNotice inner =>
    simp only [encode, DirectedOrderNotice.encode_length]
    omega
  | excludedInstrumentNotice inner =>
    simp only [encode, ExcludedInstrumentNotice.encode_length]
    omega
  | groupStateChange inner =>
    simp only [encode, GroupStateChange.encode_length]
    omega
  | legExecutionNotice inner =>
    simp only [encode, LegExecutionNotice.encode_length]
    omega
  | cancellationOfAllQuotesNotices inner =>
    simp only [encode, CancellationOfAllQuotesNotices.encode_length]
    omega
  | qualityMarketMakerNotification inner =>
    simp only [encode, QualityMarketMakerNotification.encode_length]
    omega
  | executionNotice inner =>
    simp only [encode, ExecutionNotice.encode_length]
    omega
  | quoteNotice inner =>
    simp only [encode, QuoteNotice.encode_length]
    omega
  | executionCancellationNotice inner =>
    simp only [encode, ExecutionCancellationNotice.encode_length]
    omega
  | legExecutionCancellationNotice inner =>
    simp only [encode, LegExecutionCancellationNotice.encode_length]
    omega
  | orderCancellationNoticeBySystem inner =>
    simp only [encode, OrderCancellationNoticeBySystem.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ExchangeMessage × List UInt8) :=
  if tag = 21576 then (HeartbeatQuestion.decode bytes).map fun (message, rest) => (.heartbeatQuestion message, rest)
  else if tag = 21583 then (OutOfSequence.decode bytes).map fun (message, rest) => (.outOfSequence message, rest)
  else if tag = 21573 then (TechnicalErrorNotice.decode bytes).map fun (message, rest) => (.technicalErrorNotice message, rest)
  else if tag = 21581 then (DisconnectionInstructionAcknowledgement.decode bytes).map fun (message, rest) => (.disconnectionInstructionAcknowledgement message, rest)
  else if tag = 21579 then (ConnectionAcknowledgement.decode bytes).map fun (message, rest) => (.connectionAcknowledgement message, rest)
  else if tag = 21580 then (DisconnectionAcknowledgement.decode bytes).map fun (message, rest) => (.disconnectionAcknowledgement message, rest)
  else if tag = 21588 then (EndOfTransmission.decode bytes).map fun (message, rest) => (.endOfTransmission message, rest)
  else if tag = 17746 then (ErrorNotice.decode bytes).map fun (message, rest) => (.errorNotice message, rest)
  else if tag = 19268 then (BulkQuoteDataAcknowledgement.decode bytes).map fun (message, rest) => (.bulkQuoteDataAcknowledgement message, rest)
  else if tag = 19269 then (OrderAcknowledgement.decode bytes).map fun (message, rest) => (.orderAcknowledgement message, rest)
  else if tag = 19271 then (GlobalCancellationConfirmation.decode bytes).map fun (message, rest) => (.globalCancellationConfirmation message, rest)
  else if tag = 19273 then (ImprovementOrderAcknowlegment.decode bytes).map fun (message, rest) => (.improvementOrderAcknowlegment message, rest)
  else if tag = 19277 then (OrderModificationAcknowledgement.decode bytes).map fun (message, rest) => (.orderModificationAcknowledgement message, rest)
  else if tag = 19278 then (NewComplexOrderInstrumentAcknowledgement.decode bytes).map fun (message, rest) => (.newComplexOrderInstrumentAcknowledgement message, rest)
  else if tag = 19279 then (StandardAcknowledgement.decode bytes).map fun (message, rest) => (.standardAcknowledgement message, rest)
  else if tag = 19284 then (ComplexOrderAuctionAcknowledgement.decode bytes).map fun (message, rest) => (.complexOrderAuctionAcknowledgement message, rest)
  else if tag = 19289 then (AuctionOrImprovementCancellationAcknowledgement.decode bytes).map fun (message, rest) => (.auctionOrImprovementCancellationAcknowledgement message, rest)
  else if tag = 19290 then (OrderCancellationAcknowledgement.decode bytes).map fun (message, rest) => (.orderCancellationAcknowledgement message, rest)
  else if tag = 19521 then (BulkQuoteAcknowledgement.decode bytes).map fun (message, rest) => (.bulkQuoteAcknowledgement message, rest)
  else if tag = 19797 then (TraderStatus.decode bytes).map fun (message, rest) => (.traderStatus message, rest)
  else if tag = 20035 then (DirectedOrderCancellationNotice.decode bytes).map fun (message, rest) => (.directedOrderCancellationNotice message, rest)
  else if tag = 20036 then (DirectedOrderNotice.decode bytes).map fun (message, rest) => (.directedOrderNotice message, rest)
  else if tag = 20037 then (ExcludedInstrumentNotice.decode bytes).map fun (message, rest) => (.excludedInstrumentNotice message, rest)
  else if tag = 20039 then (GroupStateChange.decode bytes).map fun (message, rest) => (.groupStateChange message, rest)
  else if tag = 20044 then (LegExecutionNotice.decode bytes).map fun (message, rest) => (.legExecutionNotice message, rest)
  else if tag = 20048 then (CancellationOfAllQuotesNotices.decode bytes).map fun (message, rest) => (.cancellationOfAllQuotesNotices message, rest)
  else if tag = 20049 then (QualityMarketMakerNotification.decode bytes).map fun (message, rest) => (.qualityMarketMakerNotification message, rest)
  else if tag = 20052 then (ExecutionNotice.decode bytes).map fun (message, rest) => (.executionNotice message, rest)
  else if tag = 20053 then (QuoteNotice.decode bytes).map fun (message, rest) => (.quoteNotice message, rest)
  else if tag = 20056 then (ExecutionCancellationNotice.decode bytes).map fun (message, rest) => (.executionCancellationNotice message, rest)
  else if tag = 20057 then (LegExecutionCancellationNotice.decode bytes).map fun (message, rest) => (.legExecutionCancellationNotice message, rest)
  else if tag = 20058 then (OrderCancellationNoticeBySystem.decode bytes).map fun (message, rest) => (.orderCancellationNoticeBySystem message, rest)
  else none

@[simp] theorem decode_encode (message : ExchangeMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ExchangeMessage

/-- Exchange Packet -/
structure ExchangePacket where
  messageLength : BitVec 32
  messageTimestamp : Alpha 6
  userSequenceId : Alpha 8
  exchangeMessageId : Alpha 6
  gapSequenceId : Alpha 2
  systemSequenceId : Alpha 6
  exchangeMessage : ExchangeMessage
  endOfText : BitVec 8
  deriving DecidableEq, Repr

namespace ExchangePacket

def encode (message : ExchangePacket) : List UInt8 :=
  encodeUIntLE 4 message.messageLength
    ++ (encodeUInt 2 (ExchangeMessage.tag message.exchangeMessage)
    ++ (Alpha.encode message.messageTimestamp
    ++ (Alpha.encode message.userSequenceId
    ++ (Alpha.encode message.exchangeMessageId
    ++ (Alpha.encode message.gapSequenceId
    ++ (Alpha.encode message.systemSequenceId
    ++ (ExchangeMessage.encode message.exchangeMessage
    ++ (encodeUInt 1 message.endOfText))))))))

def decode (bytes : List UInt8) : Option (ExchangePacket × List UInt8) := do
  let (messageLength, bytes) ← decodeUIntLE 4 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageTimestamp, bytes) ← Alpha.decode 6 bytes
  let (userSequenceId, bytes) ← Alpha.decode 8 bytes
  let (exchangeMessageId, bytes) ← Alpha.decode 6 bytes
  let (gapSequenceId, bytes) ← Alpha.decode 2 bytes
  let (systemSequenceId, bytes) ← Alpha.decode 6 bytes
  let (exchangeMessage, bytes) ← ExchangeMessage.decode messageType bytes
  let (endOfText, bytes) ← decodeUInt 1 bytes
  pure ({ messageLength, messageTimestamp, userSequenceId, exchangeMessageId, gapSequenceId, systemSequenceId, exchangeMessage, endOfText }, bytes)

theorem encode_length_pos (message : ExchangePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExchangePacket) : (encode message).length ≤ 7041 := by
  unfold encode
  cases message.exchangeMessage with
  | heartbeatQuestion inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, HeartbeatQuestion.encode_length]
    omega
  | outOfSequence inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OutOfSequence.encode_length]
    omega
  | technicalErrorNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, TechnicalErrorNotice.encode_length]
    omega
  | disconnectionInstructionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, DisconnectionInstructionAcknowledgement.encode_length]
    omega
  | connectionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ConnectionAcknowledgement.encode_length]
    omega
  | disconnectionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, DisconnectionAcknowledgement.encode_length]
    omega
  | endOfTransmission inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, EndOfTransmission.encode_length]
    omega
  | errorNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ErrorNotice.encode_length]
    omega
  | bulkQuoteDataAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, BulkQuoteDataAcknowledgement.encode_length]
    omega
  | orderAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrderAcknowledgement.encode_length]
    omega
  | globalCancellationConfirmation inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, GlobalCancellationConfirmation.encode_length]
    omega
  | improvementOrderAcknowlegment inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ImprovementOrderAcknowlegment.encode_length]
    omega
  | orderModificationAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrderModificationAcknowledgement.encode_length]
    omega
  | newComplexOrderInstrumentAcknowledgement inner =>
    have bound_inner := NewComplexOrderInstrumentAcknowledgement.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
    omega
  | standardAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, StandardAcknowledgement.encode_length]
    omega
  | complexOrderAuctionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ComplexOrderAuctionAcknowledgement.encode_length]
    omega
  | auctionOrImprovementCancellationAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, AuctionOrImprovementCancellationAcknowledgement.encode_length]
    omega
  | orderCancellationAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrderCancellationAcknowledgement.encode_length]
    omega
  | bulkQuoteAcknowledgement inner =>
    have bound_inner := BulkQuoteAcknowledgement.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
    omega
  | traderStatus inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, TraderStatus.encode_length]
    omega
  | directedOrderCancellationNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, DirectedOrderCancellationNotice.encode_length]
    omega
  | directedOrderNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, DirectedOrderNotice.encode_length]
    omega
  | excludedInstrumentNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ExcludedInstrumentNotice.encode_length]
    omega
  | groupStateChange inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, GroupStateChange.encode_length]
    omega
  | legExecutionNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, LegExecutionNotice.encode_length]
    omega
  | cancellationOfAllQuotesNotices inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, CancellationOfAllQuotesNotices.encode_length]
    omega
  | qualityMarketMakerNotification inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, QualityMarketMakerNotification.encode_length]
    omega
  | executionNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ExecutionNotice.encode_length]
    omega
  | quoteNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, QuoteNotice.encode_length]
    omega
  | executionCancellationNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, ExecutionCancellationNotice.encode_length]
    omega
  | legExecutionCancellationNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, LegExecutionCancellationNotice.encode_length]
    omega
  | orderCancellationNoticeBySystem inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrderCancellationNoticeBySystem.encode_length]
    omega

@[simp] theorem decode_encode (message : ExchangePacket) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeMessage.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExchangePacket

end Omi.BoxBoxoptionsSolaorderentrySailV225Exchange
