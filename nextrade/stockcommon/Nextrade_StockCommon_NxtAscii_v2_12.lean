import Wire

/-!
# Nextrade Nextrade Stock Market Data Common v2.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Securities Quote 10 Level Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Securities Order Filled Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Market Operation Ts Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Issue Closing Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Triggering Removing Vi Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Closing Price Trading Quote Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Equities Snapshot 10 Level Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Investor Activities Per An Industry Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Current Movement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Program Trading Activity Per Investor Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Program Trading Information Per Issue Aggregated Information Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Program Trading Information Of Total Aggregated Information Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Market Operation Schedule Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Top Five Traders Activities Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Equities Batch Data Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Equities Batch Data Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Equities Batch Data Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Member Information Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Issue Event Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Issue Event Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Issue Event Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Block Basket Trade Data Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Investor Activities Per An Issue Eod Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Short Selling Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Brokers Acitity Information Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Trading Activity By Session Per An Issue Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NextradeNextradeStockcommonNxtasciiV212

/-- Polling Data Message: 5 bytes -/
structure PollingDataMessage where
  currentTime1MinuteInterval : Alpha 4
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace PollingDataMessage

def encode (message : PollingDataMessage) : List UInt8 :=
  Alpha.encode message.currentTime1MinuteInterval
    ++ (Alpha.encode message.endKeyword)

def decode (bytes : List UInt8) : Option (PollingDataMessage × List UInt8) := do
  let (currentTime1MinuteInterval, bytes) ← Alpha.decode 4 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ currentTime1MinuteInterval, endKeyword }, bytes)

@[simp] theorem encode_length (message : PollingDataMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : PollingDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PollingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PollingDataMessage

/-- Securities Quote 10 Level Message: 585 bytes -/
structure SecuritiesQuote10LevelMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  askLevel1Price : Alpha 11
  bidLevel1Price : Alpha 11
  askLevel1Volume : Alpha 12
  bidLevel1Volume : Alpha 12
  askLevel2Price : Alpha 11
  bidLevel2Price : Alpha 11
  askLevel2Volume : Alpha 12
  bidLevel2Volume : Alpha 12
  askLevel3Price : Alpha 11
  bidLevel3Price : Alpha 11
  askLevel3Volume : Alpha 12
  bidLevel3Volume : Alpha 12
  askLevel4Price : Alpha 11
  bidLevel4Price : Alpha 11
  askLevel4Volume : Alpha 12
  bidLevel4Volume : Alpha 12
  askLevel5Price : Alpha 11
  bidLevel5Price : Alpha 11
  askLevel5Volume : Alpha 12
  bidLevel5Volume : Alpha 12
  askLevel6Price : Alpha 11
  bidLevel6Price : Alpha 11
  askLevel6Volume : Alpha 12
  bidLevel6Volume : Alpha 12
  askLevel7Price : Alpha 11
  bidLevel7Price : Alpha 11
  askLevel7Volume : Alpha 12
  bidLevel7Volume : Alpha 12
  askLevel8Price : Alpha 11
  bidLevel8Price : Alpha 11
  askLevel8Volume : Alpha 12
  bidLevel8Volume : Alpha 12
  askLevel9Price : Alpha 11
  bidLevel9Price : Alpha 11
  askLevel9Volume : Alpha 12
  bidLevel9Volume : Alpha 12
  askLevel10Price : Alpha 11
  bidLevel10Price : Alpha 11
  askLevel10Volume : Alpha 12
  bidLevel10Volume : Alpha 12
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  estimatedTradingPrice : Alpha 11
  estimatedTradingVolume : Alpha 12
  midPrice : Alpha 11
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : Alpha 12
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesQuote10LevelMessage

def encode (message : SecuritiesQuote10LevelMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (Alpha.encode message.askLevel1Volume
    ++ (Alpha.encode message.bidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (Alpha.encode message.askLevel2Volume
    ++ (Alpha.encode message.bidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (Alpha.encode message.askLevel3Volume
    ++ (Alpha.encode message.bidLevel3Volume
    ++ (Alpha.encode message.askLevel4Price
    ++ (Alpha.encode message.bidLevel4Price
    ++ (Alpha.encode message.askLevel4Volume
    ++ (Alpha.encode message.bidLevel4Volume
    ++ (Alpha.encode message.askLevel5Price
    ++ (Alpha.encode message.bidLevel5Price
    ++ (Alpha.encode message.askLevel5Volume
    ++ (Alpha.encode message.bidLevel5Volume
    ++ (Alpha.encode message.askLevel6Price
    ++ (Alpha.encode message.bidLevel6Price
    ++ (Alpha.encode message.askLevel6Volume
    ++ (Alpha.encode message.bidLevel6Volume
    ++ (Alpha.encode message.askLevel7Price
    ++ (Alpha.encode message.bidLevel7Price
    ++ (Alpha.encode message.askLevel7Volume
    ++ (Alpha.encode message.bidLevel7Volume
    ++ (Alpha.encode message.askLevel8Price
    ++ (Alpha.encode message.bidLevel8Price
    ++ (Alpha.encode message.askLevel8Volume
    ++ (Alpha.encode message.bidLevel8Volume
    ++ (Alpha.encode message.askLevel9Price
    ++ (Alpha.encode message.bidLevel9Price
    ++ (Alpha.encode message.askLevel9Volume
    ++ (Alpha.encode message.bidLevel9Volume
    ++ (Alpha.encode message.askLevel10Price
    ++ (Alpha.encode message.bidLevel10Price
    ++ (Alpha.encode message.askLevel10Volume
    ++ (Alpha.encode message.bidLevel10Volume
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (Alpha.encode message.estimatedTradingVolume
    ++ (Alpha.encode message.midPrice
    ++ (Alpha.encode message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (Alpha.encode message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecuritiesQuote10LevelMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 11 bytes
  let (estimatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (midPrice, bytes) ← Alpha.decode 11 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, askLevel4Price, bidLevel4Price, askLevel4Volume, bidLevel4Volume, askLevel5Price, bidLevel5Price, askLevel5Volume, bidLevel5Volume, askLevel6Price, bidLevel6Price, askLevel6Volume, bidLevel6Volume, askLevel7Price, bidLevel7Price, askLevel7Volume, bidLevel7Volume, askLevel8Price, bidLevel8Price, askLevel8Volume, bidLevel8Volume, askLevel9Price, bidLevel9Price, askLevel9Volume, bidLevel9Volume, askLevel10Price, bidLevel10Price, askLevel10Volume, bidLevel10Volume, totalAskVolume, totalBidVolume, estimatedTradingPrice, estimatedTradingVolume, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesQuote10LevelMessage) : (encode message).length = 585 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesQuote10LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecuritiesQuote10LevelMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecuritiesQuote10LevelMessage

/-- Securities Order Filled Message: 181 bytes -/
structure SecuritiesOrderFilledMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 11
  tradingPrice : Alpha 11
  tradingVolume : Alpha 10
  openingPrice : Alpha 11
  todaysHigh : Alpha 11
  todaysLow : Alpha 11
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  finalAskBidTypeCode : Alpha 1
  lpHoldingQuantity : Alpha 15
  theBestAsk : Alpha 11
  theBestBid : Alpha 11
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesOrderFilledMessage

def encode (message : SecuritiesOrderFilledMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.tradingPrice
    ++ (Alpha.encode message.tradingVolume
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (Alpha.encode message.lpHoldingQuantity
    ++ (Alpha.encode message.theBestAsk
    ++ (Alpha.encode message.theBestBid
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))

def decode (bytes : List UInt8) : Option (SecuritiesOrderFilledMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 11 bytes
  let (tradingPrice, bytes) ← Alpha.decode 11 bytes
  let (tradingVolume, bytes) ← Alpha.decode 10 bytes
  let (openingPrice, bytes) ← Alpha.decode 11 bytes
  let (todaysHigh, bytes) ← Alpha.decode 11 bytes
  let (todaysLow, bytes) ← Alpha.decode 11 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpHoldingQuantity, bytes) ← Alpha.decode 15 bytes
  let (theBestAsk, bytes) ← Alpha.decode 11 bytes
  let (theBestBid, bytes) ← Alpha.decode 11 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, tradingPrice, tradingVolume, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, lpHoldingQuantity, theBestAsk, theBestBid, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesOrderFilledMessage) : (encode message).length = 181 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesOrderFilledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuritiesOrderFilledMessage) (rest : List UInt8) :
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

end SecuritiesOrderFilledMessage

/-- Market Operation Ts Message: 63 bytes -/
structure MarketOperationTsMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : Alpha 5
  tradingHaltReasonCode : Alpha 3
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MarketOperationTsMessage

def encode (message : MarketOperationTsMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (Alpha.encode message.boardEventGroupCode
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (Alpha.encode message.endKeyword))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationTsMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← Alpha.decode 5 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, tradingHaltReasonCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationTsMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationTsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationTsMessage) (rest : List UInt8) :
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

end MarketOperationTsMessage

/-- Issue Closing Message: 107 bytes -/
structure IssueClosingMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  closingPrice : Alpha 11
  closingPriceTypeCode : Alpha 1
  upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 11
  lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 11
  closingPriceWeightedStockPriceAverage : Alpha 11
  closingPriceBasePriceOfBuyIn : Alpha 11
  closingPriceUpperLimitOfBuyIn : Alpha 11
  closingPriceLowerLimitOfBuyIn : Alpha 11
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace IssueClosingMessage

def encode (message : IssueClosingMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.closingPriceWeightedStockPriceAverage
    ++ (Alpha.encode message.closingPriceBasePriceOfBuyIn
    ++ (Alpha.encode message.closingPriceUpperLimitOfBuyIn
    ++ (Alpha.encode message.closingPriceLowerLimitOfBuyIn
    ++ (Alpha.encode message.endKeyword))))))))))))

def decode (bytes : List UInt8) : Option (IssueClosingMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (closingPrice, bytes) ← Alpha.decode 11 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 11 bytes
  let (lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 11 bytes
  let (closingPriceWeightedStockPriceAverage, bytes) ← Alpha.decode 11 bytes
  let (closingPriceBasePriceOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (closingPriceUpperLimitOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (closingPriceLowerLimitOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, closingPrice, closingPriceTypeCode, upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, closingPriceWeightedStockPriceAverage, closingPriceBasePriceOfBuyIn, closingPriceUpperLimitOfBuyIn, closingPriceLowerLimitOfBuyIn, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueClosingMessage) : (encode message).length = 107 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IssueClosingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueClosingMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IssueClosingMessage

/-- Triggering Removing Vi Message: 111 bytes -/
structure TriggeringRemovingViMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  theTimeEndingVi : Alpha 9
  viStatusCode : Alpha 1
  viTypeCode : Alpha 1
  aBasePriceToTriggerStaticVi : Alpha 11
  aBasePriceToTriggerDynamicVi : Alpha 11
  viTriggeringPrice : Alpha 11
  disparateRatioToTriggerStaticVi : Alpha 13
  disparateRatioToTriggerDynamicVi : Alpha 13
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace TriggeringRemovingViMessage

def encode (message : TriggeringRemovingViMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.theTimeEndingVi
    ++ (Alpha.encode message.viStatusCode
    ++ (Alpha.encode message.viTypeCode
    ++ (Alpha.encode message.aBasePriceToTriggerStaticVi
    ++ (Alpha.encode message.aBasePriceToTriggerDynamicVi
    ++ (Alpha.encode message.viTriggeringPrice
    ++ (Alpha.encode message.disparateRatioToTriggerStaticVi
    ++ (Alpha.encode message.disparateRatioToTriggerDynamicVi
    ++ (Alpha.encode message.endKeyword)))))))))))))

def decode (bytes : List UInt8) : Option (TriggeringRemovingViMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (theTimeEndingVi, bytes) ← Alpha.decode 9 bytes
  let (viStatusCode, bytes) ← Alpha.decode 1 bytes
  let (viTypeCode, bytes) ← Alpha.decode 1 bytes
  let (aBasePriceToTriggerStaticVi, bytes) ← Alpha.decode 11 bytes
  let (aBasePriceToTriggerDynamicVi, bytes) ← Alpha.decode 11 bytes
  let (viTriggeringPrice, bytes) ← Alpha.decode 11 bytes
  let (disparateRatioToTriggerStaticVi, bytes) ← Alpha.decode 13 bytes
  let (disparateRatioToTriggerDynamicVi, bytes) ← Alpha.decode 13 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, theTimeEndingVi, viStatusCode, viTypeCode, aBasePriceToTriggerStaticVi, aBasePriceToTriggerDynamicVi, viTriggeringPrice, disparateRatioToTriggerStaticVi, disparateRatioToTriggerDynamicVi, endKeyword }, bytes)

@[simp] theorem encode_length (message : TriggeringRemovingViMessage) : (encode message).length = 111 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TriggeringRemovingViMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TriggeringRemovingViMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TriggeringRemovingViMessage

/-- Closing Price Trading Quote Message: 53 bytes -/
structure ClosingPriceTradingQuoteMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ClosingPriceTradingQuoteMessage

def encode (message : ClosingPriceTradingQuoteMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (ClosingPriceTradingQuoteMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, totalAskVolume, totalBidVolume, endKeyword }, bytes)

@[simp] theorem encode_length (message : ClosingPriceTradingQuoteMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceTradingQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceTradingQuoteMessage) (rest : List UInt8) :
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

end ClosingPriceTradingQuoteMessage

/-- Equities Snapshot 10 Level Message: 680 bytes -/
structure EquitiesSnapshot10LevelMessage where
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 11
  upperLimitPrice : Alpha 11
  lowerLimitPrice : Alpha 11
  currentPrice : Alpha 11
  openingPrice : Alpha 11
  todaysHigh : Alpha 11
  todaysLow : Alpha 11
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  finalAskBidTypeCode : Alpha 1
  askLevel1Price : Alpha 11
  bidLevel1Price : Alpha 11
  askLevel1Volume : Alpha 12
  bidLevel1Volume : Alpha 12
  askLevel2Price : Alpha 11
  bidLevel2Price : Alpha 11
  askLevel2Volume : Alpha 12
  bidLevel2Volume : Alpha 12
  askLevel3Price : Alpha 11
  bidLevel3Price : Alpha 11
  askLevel3Volume : Alpha 12
  bidLevel3Volume : Alpha 12
  askLevel4Price : Alpha 11
  bidLevel4Price : Alpha 11
  askLevel4Volume : Alpha 12
  bidLevel4Volume : Alpha 12
  askLevel5Price : Alpha 11
  bidLevel5Price : Alpha 11
  askLevel5Volume : Alpha 12
  bidLevel5Volume : Alpha 12
  askLevel6Price : Alpha 11
  bidLevel6Price : Alpha 11
  askLevel6Volume : Alpha 12
  bidLevel6Volume : Alpha 12
  askLevel7Price : Alpha 11
  bidLevel7Price : Alpha 11
  askLevel7Volume : Alpha 12
  bidLevel7Volume : Alpha 12
  askLevel8Price : Alpha 11
  bidLevel8Price : Alpha 11
  askLevel8Volume : Alpha 12
  bidLevel8Volume : Alpha 12
  askLevel9Price : Alpha 11
  bidLevel9Price : Alpha 11
  askLevel9Volume : Alpha 12
  bidLevel9Volume : Alpha 12
  askLevel10Price : Alpha 11
  bidLevel10Price : Alpha 11
  askLevel10Volume : Alpha 12
  bidLevel10Volume : Alpha 12
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  estimatedTradingPrice : Alpha 11
  estimatedTradingVolume : Alpha 12
  closingPriceTypeCode : Alpha 1
  tradingHalt : Alpha 1
  midPrice : Alpha 11
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : Alpha 12
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace EquitiesSnapshot10LevelMessage

def encode (message : EquitiesSnapshot10LevelMessage) : List UInt8 :=
  Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.upperLimitPrice
    ++ (Alpha.encode message.lowerLimitPrice
    ++ (Alpha.encode message.currentPrice
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (Alpha.encode message.askLevel1Volume
    ++ (Alpha.encode message.bidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (Alpha.encode message.askLevel2Volume
    ++ (Alpha.encode message.bidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (Alpha.encode message.askLevel3Volume
    ++ (Alpha.encode message.bidLevel3Volume
    ++ (Alpha.encode message.askLevel4Price
    ++ (Alpha.encode message.bidLevel4Price
    ++ (Alpha.encode message.askLevel4Volume
    ++ (Alpha.encode message.bidLevel4Volume
    ++ (Alpha.encode message.askLevel5Price
    ++ (Alpha.encode message.bidLevel5Price
    ++ (Alpha.encode message.askLevel5Volume
    ++ (Alpha.encode message.bidLevel5Volume
    ++ (Alpha.encode message.askLevel6Price
    ++ (Alpha.encode message.bidLevel6Price
    ++ (Alpha.encode message.askLevel6Volume
    ++ (Alpha.encode message.bidLevel6Volume
    ++ (Alpha.encode message.askLevel7Price
    ++ (Alpha.encode message.bidLevel7Price
    ++ (Alpha.encode message.askLevel7Volume
    ++ (Alpha.encode message.bidLevel7Volume
    ++ (Alpha.encode message.askLevel8Price
    ++ (Alpha.encode message.bidLevel8Price
    ++ (Alpha.encode message.askLevel8Volume
    ++ (Alpha.encode message.bidLevel8Volume
    ++ (Alpha.encode message.askLevel9Price
    ++ (Alpha.encode message.bidLevel9Price
    ++ (Alpha.encode message.askLevel9Volume
    ++ (Alpha.encode message.bidLevel9Volume
    ++ (Alpha.encode message.askLevel10Price
    ++ (Alpha.encode message.bidLevel10Price
    ++ (Alpha.encode message.askLevel10Volume
    ++ (Alpha.encode message.bidLevel10Volume
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (Alpha.encode message.estimatedTradingVolume
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.tradingHalt
    ++ (Alpha.encode message.midPrice
    ++ (Alpha.encode message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (Alpha.encode message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (Alpha.encode message.endKeyword))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EquitiesSnapshot10LevelMessage × List UInt8) := do
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 11 bytes
  let (upperLimitPrice, bytes) ← Alpha.decode 11 bytes
  let (lowerLimitPrice, bytes) ← Alpha.decode 11 bytes
  let (currentPrice, bytes) ← Alpha.decode 11 bytes
  let (openingPrice, bytes) ← Alpha.decode 11 bytes
  let (todaysHigh, bytes) ← Alpha.decode 11 bytes
  let (todaysLow, bytes) ← Alpha.decode 11 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 11 bytes
  let (estimatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (tradingHalt, bytes) ← Alpha.decode 1 bytes
  let (midPrice, bytes) ← Alpha.decode 11 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, upperLimitPrice, lowerLimitPrice, currentPrice, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, askLevel4Price, bidLevel4Price, askLevel4Volume, bidLevel4Volume, askLevel5Price, bidLevel5Price, askLevel5Volume, bidLevel5Volume, askLevel6Price, bidLevel6Price, askLevel6Volume, bidLevel6Volume, askLevel7Price, bidLevel7Price, askLevel7Volume, bidLevel7Volume, askLevel8Price, bidLevel8Price, askLevel8Volume, bidLevel8Volume, askLevel9Price, bidLevel9Price, askLevel9Volume, bidLevel9Volume, askLevel10Price, bidLevel10Price, askLevel10Volume, bidLevel10Volume, totalAskVolume, totalBidVolume, estimatedTradingPrice, estimatedTradingVolume, closingPriceTypeCode, tradingHalt, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : EquitiesSnapshot10LevelMessage) : (encode message).length = 680 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EquitiesSnapshot10LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EquitiesSnapshot10LevelMessage) (rest : List UInt8) :
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

end EquitiesSnapshot10LevelMessage

/-- Investor Activities Per An Industry Message: 100 bytes -/
structure InvestorActivitiesPerAnIndustryMessage where
  calculationTime : Alpha 6
  investorCode : Alpha 4
  interfaceIndexId : Alpha 6
  indexIsinCode : Alpha 12
  accumulatedAskTradingVolume : Alpha 12
  accumulatedAskTradingValue : Alpha 22
  accumulatedBidTradingVolume : Alpha 12
  accumulatedBidTradingValue : Alpha 22
  filler3 : Alpha 3
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace InvestorActivitiesPerAnIndustryMessage

def encode (message : InvestorActivitiesPerAnIndustryMessage) : List UInt8 :=
  Alpha.encode message.calculationTime
    ++ (Alpha.encode message.investorCode
    ++ (Alpha.encode message.interfaceIndexId
    ++ (Alpha.encode message.indexIsinCode
    ++ (Alpha.encode message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (Alpha.encode message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (Alpha.encode message.filler3
    ++ (Alpha.encode message.endKeyword)))))))))

def decode (bytes : List UInt8) : Option (InvestorActivitiesPerAnIndustryMessage × List UInt8) := do
  let (calculationTime, bytes) ← Alpha.decode 6 bytes
  let (investorCode, bytes) ← Alpha.decode 4 bytes
  let (interfaceIndexId, bytes) ← Alpha.decode 6 bytes
  let (indexIsinCode, bytes) ← Alpha.decode 12 bytes
  let (accumulatedAskTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 22 bytes
  let (accumulatedBidTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 22 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ calculationTime, investorCode, interfaceIndexId, indexIsinCode, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, filler3, endKeyword }, bytes)

@[simp] theorem encode_length (message : InvestorActivitiesPerAnIndustryMessage) : (encode message).length = 100 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InvestorActivitiesPerAnIndustryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InvestorActivitiesPerAnIndustryMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InvestorActivitiesPerAnIndustryMessage

/-- Current Movement Message: 51 bytes -/
structure CurrentMovementMessage where
  totalNumberOfIssues : Alpha 5
  numberOfIssuesForMovementCalculation : Alpha 5
  numberOfIssuesOfUpperLimit : Alpha 5
  numberOfIssuesOfGoingUp : Alpha 5
  numberOfIssuesOfSteadiness : Alpha 5
  numberOfIssuesOfLowerLimit : Alpha 5
  numberOfIssuesOfGoingDown : Alpha 5
  numberOfIssuesHavingQuotes : Alpha 5
  numberOfIssuesOfWhichQuotesAreIncreasing : Alpha 5
  numberOfIssuesOfWhichQuotesAreDecreasing : Alpha 5
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace CurrentMovementMessage

def encode (message : CurrentMovementMessage) : List UInt8 :=
  Alpha.encode message.totalNumberOfIssues
    ++ (Alpha.encode message.numberOfIssuesForMovementCalculation
    ++ (Alpha.encode message.numberOfIssuesOfUpperLimit
    ++ (Alpha.encode message.numberOfIssuesOfGoingUp
    ++ (Alpha.encode message.numberOfIssuesOfSteadiness
    ++ (Alpha.encode message.numberOfIssuesOfLowerLimit
    ++ (Alpha.encode message.numberOfIssuesOfGoingDown
    ++ (Alpha.encode message.numberOfIssuesHavingQuotes
    ++ (Alpha.encode message.numberOfIssuesOfWhichQuotesAreIncreasing
    ++ (Alpha.encode message.numberOfIssuesOfWhichQuotesAreDecreasing
    ++ (Alpha.encode message.endKeyword))))))))))

def decode (bytes : List UInt8) : Option (CurrentMovementMessage × List UInt8) := do
  let (totalNumberOfIssues, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesForMovementCalculation, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesOfUpperLimit, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesOfGoingUp, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesOfSteadiness, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesOfLowerLimit, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesOfGoingDown, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesHavingQuotes, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesOfWhichQuotesAreIncreasing, bytes) ← Alpha.decode 5 bytes
  let (numberOfIssuesOfWhichQuotesAreDecreasing, bytes) ← Alpha.decode 5 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ totalNumberOfIssues, numberOfIssuesForMovementCalculation, numberOfIssuesOfUpperLimit, numberOfIssuesOfGoingUp, numberOfIssuesOfSteadiness, numberOfIssuesOfLowerLimit, numberOfIssuesOfGoingDown, numberOfIssuesHavingQuotes, numberOfIssuesOfWhichQuotesAreIncreasing, numberOfIssuesOfWhichQuotesAreDecreasing, endKeyword }, bytes)

@[simp] theorem encode_length (message : CurrentMovementMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : CurrentMovementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CurrentMovementMessage) (rest : List UInt8) :
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

end CurrentMovementMessage

/-- Program Trading Activity Per Investor Message: 159 bytes -/
structure ProgramTradingActivityPerInvestorMessage where
  calculationTime : Alpha 6
  investorCode : Alpha 4
  sellsideArbitrageVolume : Alpha 15
  sellsideArbitrageValue : Alpha 22
  sellsideNonarbitrageVolume : Alpha 15
  sellsideNonarbitrageValue : Alpha 22
  buysideArbitrageVolume : Alpha 15
  buysideArbitrageValue : Alpha 22
  buysideNonarbitrageVolume : Alpha 15
  buysideNonarbitrageValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ProgramTradingActivityPerInvestorMessage

def encode (message : ProgramTradingActivityPerInvestorMessage) : List UInt8 :=
  Alpha.encode message.calculationTime
    ++ (Alpha.encode message.investorCode
    ++ (Alpha.encode message.sellsideArbitrageVolume
    ++ (Alpha.encode message.sellsideArbitrageValue
    ++ (Alpha.encode message.sellsideNonarbitrageVolume
    ++ (Alpha.encode message.sellsideNonarbitrageValue
    ++ (Alpha.encode message.buysideArbitrageVolume
    ++ (Alpha.encode message.buysideArbitrageValue
    ++ (Alpha.encode message.buysideNonarbitrageVolume
    ++ (Alpha.encode message.buysideNonarbitrageValue
    ++ (Alpha.encode message.endKeyword))))))))))

def decode (bytes : List UInt8) : Option (ProgramTradingActivityPerInvestorMessage × List UInt8) := do
  let (calculationTime, bytes) ← Alpha.decode 6 bytes
  let (investorCode, bytes) ← Alpha.decode 4 bytes
  let (sellsideArbitrageVolume, bytes) ← Alpha.decode 15 bytes
  let (sellsideArbitrageValue, bytes) ← Alpha.decode 22 bytes
  let (sellsideNonarbitrageVolume, bytes) ← Alpha.decode 15 bytes
  let (sellsideNonarbitrageValue, bytes) ← Alpha.decode 22 bytes
  let (buysideArbitrageVolume, bytes) ← Alpha.decode 15 bytes
  let (buysideArbitrageValue, bytes) ← Alpha.decode 22 bytes
  let (buysideNonarbitrageVolume, bytes) ← Alpha.decode 15 bytes
  let (buysideNonarbitrageValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ calculationTime, investorCode, sellsideArbitrageVolume, sellsideArbitrageValue, sellsideNonarbitrageVolume, sellsideNonarbitrageValue, buysideArbitrageVolume, buysideArbitrageValue, buysideNonarbitrageVolume, buysideNonarbitrageValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : ProgramTradingActivityPerInvestorMessage) : (encode message).length = 159 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ProgramTradingActivityPerInvestorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProgramTradingActivityPerInvestorMessage) (rest : List UInt8) :
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

end ProgramTradingActivityPerInvestorMessage

/-- Program Trading Information Per Issue Aggregated Information Message: 395 bytes -/
structure ProgramTradingInformationPerIssueAggregatedInformationMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  sellsideArbitrageTradingRemainingQuantity : Alpha 15
  buysideArbitrageTradingRemainingQuantity : Alpha 15
  sellsideNonarbitrageRemainingQuantity : Alpha 15
  buysideNonarbitrageRemainingQuantity : Alpha 15
  sellsideArbitrageQuantity : Alpha 15
  buysideArbitrageQuantity : Alpha 15
  sellsideNonarbitrageQuantity : Alpha 15
  buysideNonarbitrageQuantity : Alpha 15
  arbitrageAskTrustTradingVolume : Alpha 10
  arbitrageAskPrincipalTradingVolume : Alpha 10
  arbitrageBidTrustTradingVolume : Alpha 10
  arbitrageBidPrincipalTradingVolume : Alpha 10
  nonArbitrageAskTrustTradingVolume : Alpha 10
  nonArbitrageAskPrincipalTradingVolume : Alpha 10
  nonArbitrageBidTrustTradingVolume : Alpha 10
  nonArbitrageBidPrincipalTradingVolume : Alpha 10
  arbitrageAskTrustTradingValue : Alpha 22
  arbitrageAskPrincipalTradingValue : Alpha 22
  arbitrageBidTrustTradingValue : Alpha 22
  arbitrageBidPrincipalTradingValue : Alpha 22
  nonArbitrageAskTrustTradingValue : Alpha 22
  nonArbitrageAskPrincipalTradingValue : Alpha 22
  nonArbitrageBidTrustTradingValue : Alpha 22
  nonArbitrageBidPrincipalTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ProgramTradingInformationPerIssueAggregatedInformationMessage

def encode (message : ProgramTradingInformationPerIssueAggregatedInformationMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.sellsideArbitrageTradingRemainingQuantity
    ++ (Alpha.encode message.buysideArbitrageTradingRemainingQuantity
    ++ (Alpha.encode message.sellsideNonarbitrageRemainingQuantity
    ++ (Alpha.encode message.buysideNonarbitrageRemainingQuantity
    ++ (Alpha.encode message.sellsideArbitrageQuantity
    ++ (Alpha.encode message.buysideArbitrageQuantity
    ++ (Alpha.encode message.sellsideNonarbitrageQuantity
    ++ (Alpha.encode message.buysideNonarbitrageQuantity
    ++ (Alpha.encode message.arbitrageAskTrustTradingVolume
    ++ (Alpha.encode message.arbitrageAskPrincipalTradingVolume
    ++ (Alpha.encode message.arbitrageBidTrustTradingVolume
    ++ (Alpha.encode message.arbitrageBidPrincipalTradingVolume
    ++ (Alpha.encode message.nonArbitrageAskTrustTradingVolume
    ++ (Alpha.encode message.nonArbitrageAskPrincipalTradingVolume
    ++ (Alpha.encode message.nonArbitrageBidTrustTradingVolume
    ++ (Alpha.encode message.nonArbitrageBidPrincipalTradingVolume
    ++ (Alpha.encode message.arbitrageAskTrustTradingValue
    ++ (Alpha.encode message.arbitrageAskPrincipalTradingValue
    ++ (Alpha.encode message.arbitrageBidTrustTradingValue
    ++ (Alpha.encode message.arbitrageBidPrincipalTradingValue
    ++ (Alpha.encode message.nonArbitrageAskTrustTradingValue
    ++ (Alpha.encode message.nonArbitrageAskPrincipalTradingValue
    ++ (Alpha.encode message.nonArbitrageBidTrustTradingValue
    ++ (Alpha.encode message.nonArbitrageBidPrincipalTradingValue
    ++ (Alpha.encode message.endKeyword))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ProgramTradingInformationPerIssueAggregatedInformationMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (sellsideArbitrageTradingRemainingQuantity, bytes) ← Alpha.decode 15 bytes
  let (buysideArbitrageTradingRemainingQuantity, bytes) ← Alpha.decode 15 bytes
  let (sellsideNonarbitrageRemainingQuantity, bytes) ← Alpha.decode 15 bytes
  let (buysideNonarbitrageRemainingQuantity, bytes) ← Alpha.decode 15 bytes
  let (sellsideArbitrageQuantity, bytes) ← Alpha.decode 15 bytes
  let (buysideArbitrageQuantity, bytes) ← Alpha.decode 15 bytes
  let (sellsideNonarbitrageQuantity, bytes) ← Alpha.decode 15 bytes
  let (buysideNonarbitrageQuantity, bytes) ← Alpha.decode 15 bytes
  let (arbitrageAskTrustTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (arbitrageAskPrincipalTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (arbitrageBidTrustTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (arbitrageBidPrincipalTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (nonArbitrageAskTrustTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (nonArbitrageAskPrincipalTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (nonArbitrageBidTrustTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (nonArbitrageBidPrincipalTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (arbitrageAskTrustTradingValue, bytes) ← Alpha.decode 22 bytes
  let (arbitrageAskPrincipalTradingValue, bytes) ← Alpha.decode 22 bytes
  let (arbitrageBidTrustTradingValue, bytes) ← Alpha.decode 22 bytes
  let (arbitrageBidPrincipalTradingValue, bytes) ← Alpha.decode 22 bytes
  let (nonArbitrageAskTrustTradingValue, bytes) ← Alpha.decode 22 bytes
  let (nonArbitrageAskPrincipalTradingValue, bytes) ← Alpha.decode 22 bytes
  let (nonArbitrageBidTrustTradingValue, bytes) ← Alpha.decode 22 bytes
  let (nonArbitrageBidPrincipalTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, sellsideArbitrageTradingRemainingQuantity, buysideArbitrageTradingRemainingQuantity, sellsideNonarbitrageRemainingQuantity, buysideNonarbitrageRemainingQuantity, sellsideArbitrageQuantity, buysideArbitrageQuantity, sellsideNonarbitrageQuantity, buysideNonarbitrageQuantity, arbitrageAskTrustTradingVolume, arbitrageAskPrincipalTradingVolume, arbitrageBidTrustTradingVolume, arbitrageBidPrincipalTradingVolume, nonArbitrageAskTrustTradingVolume, nonArbitrageAskPrincipalTradingVolume, nonArbitrageBidTrustTradingVolume, nonArbitrageBidPrincipalTradingVolume, arbitrageAskTrustTradingValue, arbitrageAskPrincipalTradingValue, arbitrageBidTrustTradingValue, arbitrageBidPrincipalTradingValue, nonArbitrageAskTrustTradingValue, nonArbitrageAskPrincipalTradingValue, nonArbitrageBidTrustTradingValue, nonArbitrageBidPrincipalTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : ProgramTradingInformationPerIssueAggregatedInformationMessage) : (encode message).length = 395 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ProgramTradingInformationPerIssueAggregatedInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ProgramTradingInformationPerIssueAggregatedInformationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ProgramTradingInformationPerIssueAggregatedInformationMessage

/-- Program Trading Information Of Total Aggregated Information Message: 377 bytes -/
structure ProgramTradingInformationOfTotalAggregatedInformationMessage where
  sellsideArbitrageTradingRemainingQuantity : Alpha 15
  buysideArbitrageTradingRemainingQuantity : Alpha 15
  sellsideNonarbitrageRemainingQuantity : Alpha 15
  buysideNonarbitrageRemainingQuantity : Alpha 15
  sellsideArbitrageQuantity : Alpha 15
  buysideArbitrageQuantity : Alpha 15
  sellsideNonarbitrageQuantity : Alpha 15
  buysideNonarbitrageQuantity : Alpha 15
  arbitrageAskTrustTradingVolume : Alpha 10
  arbitrageAskPrincipalTradingVolume : Alpha 10
  arbitrageBidTrustTradingVolume : Alpha 10
  arbitrageBidPrincipalTradingVolume : Alpha 10
  nonArbitrageAskTrustTradingVolume : Alpha 10
  nonArbitrageAskPrincipalTradingVolume : Alpha 10
  nonArbitrageBidTrustTradingVolume : Alpha 10
  nonArbitrageBidPrincipalTradingVolume : Alpha 10
  arbitrageAskTrustTradingValue : Alpha 22
  arbitrageAskPrincipalTradingValue : Alpha 22
  arbitrageBidTrustTradingValue : Alpha 22
  arbitrageBidPrincipalTradingValue : Alpha 22
  nonArbitrageAskTrustTradingValue : Alpha 22
  nonArbitrageAskPrincipalTradingValue : Alpha 22
  nonArbitrageBidTrustTradingValue : Alpha 22
  nonArbitrageBidPrincipalTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ProgramTradingInformationOfTotalAggregatedInformationMessage

def encode (message : ProgramTradingInformationOfTotalAggregatedInformationMessage) : List UInt8 :=
  Alpha.encode message.sellsideArbitrageTradingRemainingQuantity
    ++ (Alpha.encode message.buysideArbitrageTradingRemainingQuantity
    ++ (Alpha.encode message.sellsideNonarbitrageRemainingQuantity
    ++ (Alpha.encode message.buysideNonarbitrageRemainingQuantity
    ++ (Alpha.encode message.sellsideArbitrageQuantity
    ++ (Alpha.encode message.buysideArbitrageQuantity
    ++ (Alpha.encode message.sellsideNonarbitrageQuantity
    ++ (Alpha.encode message.buysideNonarbitrageQuantity
    ++ (Alpha.encode message.arbitrageAskTrustTradingVolume
    ++ (Alpha.encode message.arbitrageAskPrincipalTradingVolume
    ++ (Alpha.encode message.arbitrageBidTrustTradingVolume
    ++ (Alpha.encode message.arbitrageBidPrincipalTradingVolume
    ++ (Alpha.encode message.nonArbitrageAskTrustTradingVolume
    ++ (Alpha.encode message.nonArbitrageAskPrincipalTradingVolume
    ++ (Alpha.encode message.nonArbitrageBidTrustTradingVolume
    ++ (Alpha.encode message.nonArbitrageBidPrincipalTradingVolume
    ++ (Alpha.encode message.arbitrageAskTrustTradingValue
    ++ (Alpha.encode message.arbitrageAskPrincipalTradingValue
    ++ (Alpha.encode message.arbitrageBidTrustTradingValue
    ++ (Alpha.encode message.arbitrageBidPrincipalTradingValue
    ++ (Alpha.encode message.nonArbitrageAskTrustTradingValue
    ++ (Alpha.encode message.nonArbitrageAskPrincipalTradingValue
    ++ (Alpha.encode message.nonArbitrageBidTrustTradingValue
    ++ (Alpha.encode message.nonArbitrageBidPrincipalTradingValue
    ++ (Alpha.encode message.endKeyword))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ProgramTradingInformationOfTotalAggregatedInformationMessage × List UInt8) := do
  let (sellsideArbitrageTradingRemainingQuantity, bytes) ← Alpha.decode 15 bytes
  let (buysideArbitrageTradingRemainingQuantity, bytes) ← Alpha.decode 15 bytes
  let (sellsideNonarbitrageRemainingQuantity, bytes) ← Alpha.decode 15 bytes
  let (buysideNonarbitrageRemainingQuantity, bytes) ← Alpha.decode 15 bytes
  let (sellsideArbitrageQuantity, bytes) ← Alpha.decode 15 bytes
  let (buysideArbitrageQuantity, bytes) ← Alpha.decode 15 bytes
  let (sellsideNonarbitrageQuantity, bytes) ← Alpha.decode 15 bytes
  let (buysideNonarbitrageQuantity, bytes) ← Alpha.decode 15 bytes
  let (arbitrageAskTrustTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (arbitrageAskPrincipalTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (arbitrageBidTrustTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (arbitrageBidPrincipalTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (nonArbitrageAskTrustTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (nonArbitrageAskPrincipalTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (nonArbitrageBidTrustTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (nonArbitrageBidPrincipalTradingVolume, bytes) ← Alpha.decode 10 bytes
  let (arbitrageAskTrustTradingValue, bytes) ← Alpha.decode 22 bytes
  let (arbitrageAskPrincipalTradingValue, bytes) ← Alpha.decode 22 bytes
  let (arbitrageBidTrustTradingValue, bytes) ← Alpha.decode 22 bytes
  let (arbitrageBidPrincipalTradingValue, bytes) ← Alpha.decode 22 bytes
  let (nonArbitrageAskTrustTradingValue, bytes) ← Alpha.decode 22 bytes
  let (nonArbitrageAskPrincipalTradingValue, bytes) ← Alpha.decode 22 bytes
  let (nonArbitrageBidTrustTradingValue, bytes) ← Alpha.decode 22 bytes
  let (nonArbitrageBidPrincipalTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ sellsideArbitrageTradingRemainingQuantity, buysideArbitrageTradingRemainingQuantity, sellsideNonarbitrageRemainingQuantity, buysideNonarbitrageRemainingQuantity, sellsideArbitrageQuantity, buysideArbitrageQuantity, sellsideNonarbitrageQuantity, buysideNonarbitrageQuantity, arbitrageAskTrustTradingVolume, arbitrageAskPrincipalTradingVolume, arbitrageBidTrustTradingVolume, arbitrageBidPrincipalTradingVolume, nonArbitrageAskTrustTradingVolume, nonArbitrageAskPrincipalTradingVolume, nonArbitrageBidTrustTradingVolume, nonArbitrageBidPrincipalTradingVolume, arbitrageAskTrustTradingValue, arbitrageAskPrincipalTradingValue, arbitrageBidTrustTradingValue, arbitrageBidPrincipalTradingValue, nonArbitrageAskTrustTradingValue, nonArbitrageAskPrincipalTradingValue, nonArbitrageBidTrustTradingValue, nonArbitrageBidPrincipalTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : ProgramTradingInformationOfTotalAggregatedInformationMessage) : (encode message).length = 377 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ProgramTradingInformationOfTotalAggregatedInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ProgramTradingInformationOfTotalAggregatedInformationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ProgramTradingInformationOfTotalAggregatedInformationMessage

/-- Market Operation Schedule Message: 78 bytes -/
structure MarketOperationScheduleMessage where
  marketOperationProductId : Alpha 3
  boardId : Alpha 2
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : Alpha 5
  sessionStartEndCode : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  isinCodeOfACommonStock : Alpha 12
  productId : Alpha 11
  tradingHaltReasonCode : Alpha 3
  tradingHaltTypeCode : Alpha 1
  stepApplied : Alpha 2
  priceLimitRangeExpansionForBaseIssueTypeCode : Alpha 1
  expectedTimeOfExpandingPriceLimitRange : Alpha 9
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MarketOperationScheduleMessage

def encode (message : MarketOperationScheduleMessage) : List UInt8 :=
  Alpha.encode message.marketOperationProductId
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (Alpha.encode message.boardEventGroupCode
    ++ (Alpha.encode message.sessionStartEndCode
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.isinCodeOfACommonStock
    ++ (Alpha.encode message.productId
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (Alpha.encode message.tradingHaltTypeCode
    ++ (Alpha.encode message.stepApplied
    ++ (Alpha.encode message.priceLimitRangeExpansionForBaseIssueTypeCode
    ++ (Alpha.encode message.expectedTimeOfExpandingPriceLimitRange
    ++ (Alpha.encode message.endKeyword)))))))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationScheduleMessage × List UInt8) := do
  let (marketOperationProductId, bytes) ← Alpha.decode 3 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← Alpha.decode 5 bytes
  let (sessionStartEndCode, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (isinCodeOfACommonStock, bytes) ← Alpha.decode 12 bytes
  let (productId, bytes) ← Alpha.decode 11 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (tradingHaltTypeCode, bytes) ← Alpha.decode 1 bytes
  let (stepApplied, bytes) ← Alpha.decode 2 bytes
  let (priceLimitRangeExpansionForBaseIssueTypeCode, bytes) ← Alpha.decode 1 bytes
  let (expectedTimeOfExpandingPriceLimitRange, bytes) ← Alpha.decode 9 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ marketOperationProductId, boardId, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, sessionStartEndCode, sessionId, isinCode, isinCodeOfACommonStock, productId, tradingHaltReasonCode, tradingHaltTypeCode, stepApplied, priceLimitRangeExpansionForBaseIssueTypeCode, expectedTimeOfExpandingPriceLimitRange, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationScheduleMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationScheduleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationScheduleMessage) (rest : List UInt8) :
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

end MarketOperationScheduleMessage

/-- Member Firm Imposing Lifting Sanctions Message: 41 bytes -/
structure MemberFirmImposingLiftingSanctionsMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  disclosingDataTypeCode : Alpha 3
  disclosureTime : Alpha 9
  memberNumber : Alpha 5
  memberFirmTrustPrincipalTypeCode : Alpha 5
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MemberFirmImposingLiftingSanctionsMessage

def encode (message : MemberFirmImposingLiftingSanctionsMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.disclosingDataTypeCode
    ++ (Alpha.encode message.disclosureTime
    ++ (Alpha.encode message.memberNumber
    ++ (Alpha.encode message.memberFirmTrustPrincipalTypeCode
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (MemberFirmImposingLiftingSanctionsMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (disclosingDataTypeCode, bytes) ← Alpha.decode 3 bytes
  let (disclosureTime, bytes) ← Alpha.decode 9 bytes
  let (memberNumber, bytes) ← Alpha.decode 5 bytes
  let (memberFirmTrustPrincipalTypeCode, bytes) ← Alpha.decode 5 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, disclosingDataTypeCode, disclosureTime, memberNumber, memberFirmTrustPrincipalTypeCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MemberFirmImposingLiftingSanctionsMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MemberFirmImposingLiftingSanctionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MemberFirmImposingLiftingSanctionsMessage) (rest : List UInt8) :
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

end MemberFirmImposingLiftingSanctionsMessage

/-- Top Five Traders Activities Message: 409 bytes -/
structure TopFiveTradersActivitiesMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  memberNumber1ForAsk : Alpha 5
  askTradingVolume1 : Alpha 12
  askTradingValue1 : Alpha 22
  memberNumber1ForBid : Alpha 5
  bidTradingVolume1 : Alpha 12
  bidTradingValue1 : Alpha 22
  memberNumber2ForAsk : Alpha 5
  askTradingVolume2 : Alpha 12
  askTradingValue2 : Alpha 22
  memberNumber2ForBid : Alpha 5
  bidTradingVolume2 : Alpha 12
  bidTradingValue2 : Alpha 22
  memberNumber3ForAsk : Alpha 5
  askTradingVolume3 : Alpha 12
  askTradingValue3 : Alpha 22
  memberNumber3ForBid : Alpha 5
  bidTradingVolume3 : Alpha 12
  bidTradingValue3 : Alpha 22
  memberNumber4ForAsk : Alpha 5
  askTradingVolume4 : Alpha 12
  askTradingValue4 : Alpha 22
  memberNumber4ForBid : Alpha 5
  bidTradingVolume4 : Alpha 12
  bidTradingValue4 : Alpha 22
  memberNumber5ForAsk : Alpha 5
  askTradingVolume5 : Alpha 12
  askTradingValue5 : Alpha 22
  memberNumber5ForBid : Alpha 5
  bidTradingVolume5 : Alpha 12
  bidTradingValue5 : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace TopFiveTradersActivitiesMessage

def encode (message : TopFiveTradersActivitiesMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.memberNumber1ForAsk
    ++ (Alpha.encode message.askTradingVolume1
    ++ (Alpha.encode message.askTradingValue1
    ++ (Alpha.encode message.memberNumber1ForBid
    ++ (Alpha.encode message.bidTradingVolume1
    ++ (Alpha.encode message.bidTradingValue1
    ++ (Alpha.encode message.memberNumber2ForAsk
    ++ (Alpha.encode message.askTradingVolume2
    ++ (Alpha.encode message.askTradingValue2
    ++ (Alpha.encode message.memberNumber2ForBid
    ++ (Alpha.encode message.bidTradingVolume2
    ++ (Alpha.encode message.bidTradingValue2
    ++ (Alpha.encode message.memberNumber3ForAsk
    ++ (Alpha.encode message.askTradingVolume3
    ++ (Alpha.encode message.askTradingValue3
    ++ (Alpha.encode message.memberNumber3ForBid
    ++ (Alpha.encode message.bidTradingVolume3
    ++ (Alpha.encode message.bidTradingValue3
    ++ (Alpha.encode message.memberNumber4ForAsk
    ++ (Alpha.encode message.askTradingVolume4
    ++ (Alpha.encode message.askTradingValue4
    ++ (Alpha.encode message.memberNumber4ForBid
    ++ (Alpha.encode message.bidTradingVolume4
    ++ (Alpha.encode message.bidTradingValue4
    ++ (Alpha.encode message.memberNumber5ForAsk
    ++ (Alpha.encode message.askTradingVolume5
    ++ (Alpha.encode message.askTradingValue5
    ++ (Alpha.encode message.memberNumber5ForBid
    ++ (Alpha.encode message.bidTradingVolume5
    ++ (Alpha.encode message.bidTradingValue5
    ++ (Alpha.encode message.endKeyword))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TopFiveTradersActivitiesMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (memberNumber1ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume1, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue1, bytes) ← Alpha.decode 22 bytes
  let (memberNumber1ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume1, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue1, bytes) ← Alpha.decode 22 bytes
  let (memberNumber2ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume2, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue2, bytes) ← Alpha.decode 22 bytes
  let (memberNumber2ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume2, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue2, bytes) ← Alpha.decode 22 bytes
  let (memberNumber3ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume3, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue3, bytes) ← Alpha.decode 22 bytes
  let (memberNumber3ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume3, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue3, bytes) ← Alpha.decode 22 bytes
  let (memberNumber4ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume4, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue4, bytes) ← Alpha.decode 22 bytes
  let (memberNumber4ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume4, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue4, bytes) ← Alpha.decode 22 bytes
  let (memberNumber5ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume5, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue5, bytes) ← Alpha.decode 22 bytes
  let (memberNumber5ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume5, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue5, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, memberNumber1ForAsk, askTradingVolume1, askTradingValue1, memberNumber1ForBid, bidTradingVolume1, bidTradingValue1, memberNumber2ForAsk, askTradingVolume2, askTradingValue2, memberNumber2ForBid, bidTradingVolume2, bidTradingValue2, memberNumber3ForAsk, askTradingVolume3, askTradingValue3, memberNumber3ForBid, bidTradingVolume3, bidTradingValue3, memberNumber4ForAsk, askTradingVolume4, askTradingValue4, memberNumber4ForBid, bidTradingVolume4, bidTradingValue4, memberNumber5ForAsk, askTradingVolume5, askTradingValue5, memberNumber5ForBid, bidTradingVolume5, bidTradingValue5, endKeyword }, bytes)

@[simp] theorem encode_length (message : TopFiveTradersActivitiesMessage) : (encode message).length = 409 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TopFiveTradersActivitiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TopFiveTradersActivitiesMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TopFiveTradersActivitiesMessage

/-- Equities Batch Data Message: 649 bytes -/
structure EquitiesBatchDataMessage where
  messageSequenceNumber : Alpha 8
  totalNumberOfInstrumentsOfTheContract : Alpha 6
  businessDate : Alpha 8
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  abbreviatedIssueCode : Alpha 9
  abbreviatedIssueName : Alpha 40
  abbreviatedIssueNameInEn : Alpha 40
  groupNumber : Alpha 5
  marketOperationProductId : Alpha 3
  securityGroupId : Alpha 2
  unitTrading : Alpha 1
  rightsTypeCode : Alpha 2
  parValueTypeCode : Alpha 2
  anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice : Alpha 1
  reevaluationReasonCode : Alpha 2
  basePriceChange : Alpha 1
  randomEndTriggerCode : Alpha 1
  marketAlert : Alpha 1
  marketAlertTypeCode : Alpha 2
  koreaCorporateGovernanceStockPriceIndexKogi : Alpha 1
  issueForAdministration : Alpha 1
  unfaithfulDisclosure : Alpha 1
  backdoorListing : Alpha 1
  tradingHalt : Alpha 1
  industryId : Alpha 10
  smallMediumSizedBusiness : Alpha 1
  sectionTypeCode : Alpha 1
  investmentInstitutionTypeCode : Alpha 1
  basePrice : Alpha 11
  yesterdaysClosingPriceTypeCodeKrx : Alpha 1
  yesterdaysClosingPriceKrx : Alpha 11
  yesterdaysAccumulatedTradingAmount : Alpha 12
  yesterdaysAccumulatedTradingValue : Alpha 22
  upperLimitPrice : Alpha 11
  lowerLimitPrice : Alpha 11
  substitutePriceOfSecurities : Alpha 11
  parValue : Alpha 11
  issuingPrice : Alpha 11
  listingDate : Alpha 8
  numberOfListedShares : Alpha 16
  liquidationTrade : Alpha 1
  theEstablishmentDate : Alpha 8
  maturityDate : Alpha 8
  exercisingPeriod : Alpha 8
  expirationDateForRight : Alpha 8
  exercisePriceOfElwOrBw : Alpha 13
  capital : Alpha 22
  creditOrderPossibility : Alpha 1
  limitOrderPermissionTypeCode : Alpha 5
  marketPriceOrderPermissionTypeCode : Alpha 5
  conditionedOrderPermissionTypeCode : Alpha 5
  bestFavorableOrderPermissionTypeCode : Alpha 5
  firstBestOrderPermissionType : Alpha 5
  midPriceOrderPermissionTypeCode : Alpha 5
  stopLimitPriceOrderPermissionTypeCode : Alpha 5
  capitalIncreaseTypeCode : Alpha 2
  otherStockTypeCode : Alpha 1
  nationalStock : Alpha 1
  appraisedPrice : Alpha 11
  lowestOrderPrice : Alpha 11
  highestOrderPrice : Alpha 11
  unitOfVolumeInMainBoard : Alpha 11
  lotSizeAfterhoursTrading : Alpha 11
  reiTsTypeCode : Alpha 1
  targetStockIsinCode : Alpha 12
  currencyIsoCode : Alpha 3
  countryCode : Alpha 3
  marketMakingPossibility : Alpha 1
  closingPriceTradingPossibilityInTheAfterHours : Alpha 1
  closingPriceTradingInThePreopeningMarket : Alpha 1
  blockTradingInThePreopeningMarket : Alpha 1
  basketTradingInThePreopeningMarket : Alpha 1
  announcementOfEstimatedTradingPrice : Alpha 1
  shortSelling : Alpha 1
  etfTrackingDifference : Alpha 13
  regs : Alpha 1
  spac : Alpha 1
  taxTypeCode : Alpha 1
  appraisalRatioOfSubstitutePrice : Alpha 13
  investmentCautionIssue : Alpha 1
  delistingDate : Alpha 8
  shorttermOverheatIssueTypeCode : Alpha 1
  etfReplicationMethodsTypeCode : Alpha 1
  expirationDate : Alpha 8
  distributionTypeCode : Alpha 2
  calculationOfRedemptionPriceStartDate : Alpha 8
  calculationOfRedemptionPriceEndDate : Alpha 8
  etpProductTypeCode : Alpha 1
  indexCalculationInstitutionTypeCode : Alpha 2
  indexMarketClassificationId : Alpha 6
  indexSequenceNumber : Alpha 3
  trackingIndexLeverageInverseTypeCode : Alpha 2
  referenceIndexLeverageInverseTypeCode : Alpha 2
  indexAssetClassificationId1 : Alpha 6
  indexAssetClassificationId2 : Alpha 6
  ipoUnderwriterMemberNumber : Alpha 5
  lpOrder : Alpha 1
  lowLiquidity : Alpha 1
  abnormalRise : Alpha 1
  upperLimitQuantity : Alpha 23
  investmentPrecautionIssue : Alpha 1
  preferredStocksWithLesserShares : Alpha 1
  spacMerger : Alpha 1
  segmentTypeCode : Alpha 1
  afterMarketPossibility : Alpha 1
  choiceOnCompetitiveTrading : Alpha 1
  limitOnCompetitiveTradingVolume : Alpha 1
  occurrenceOfReasonsProhibitingCompetitiveTrading : Alpha 1
  approvalOnCompetitiveTrading : Alpha 1
  approvalOnNegotiationTrading : Alpha 1
  yesterdaysClosingPriceTypeCodeNxt : Alpha 1
  yesterdaysClosingPriceNxt : Alpha 11
  competitionBoardTradePermissionCode : Alpha 5
  negotiationPossibleOrNotBeforeMainMarket : Alpha 1
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace EquitiesBatchDataMessage

def encode (message : EquitiesBatchDataMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.totalNumberOfInstrumentsOfTheContract
    ++ (Alpha.encode message.businessDate
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.abbreviatedIssueCode
    ++ (Alpha.encode message.abbreviatedIssueName
    ++ (Alpha.encode message.abbreviatedIssueNameInEn
    ++ (Alpha.encode message.groupNumber
    ++ (Alpha.encode message.marketOperationProductId
    ++ (Alpha.encode message.securityGroupId
    ++ (Alpha.encode message.unitTrading
    ++ (Alpha.encode message.rightsTypeCode
    ++ (Alpha.encode message.parValueTypeCode
    ++ (Alpha.encode message.anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice
    ++ (Alpha.encode message.reevaluationReasonCode
    ++ (Alpha.encode message.basePriceChange
    ++ (Alpha.encode message.randomEndTriggerCode
    ++ (Alpha.encode message.marketAlert
    ++ (Alpha.encode message.marketAlertTypeCode
    ++ (Alpha.encode message.koreaCorporateGovernanceStockPriceIndexKogi
    ++ (Alpha.encode message.issueForAdministration
    ++ (Alpha.encode message.unfaithfulDisclosure
    ++ (Alpha.encode message.backdoorListing
    ++ (Alpha.encode message.tradingHalt
    ++ (Alpha.encode message.industryId
    ++ (Alpha.encode message.smallMediumSizedBusiness
    ++ (Alpha.encode message.sectionTypeCode
    ++ (Alpha.encode message.investmentInstitutionTypeCode
    ++ (Alpha.encode message.basePrice
    ++ (Alpha.encode message.yesterdaysClosingPriceTypeCodeKrx
    ++ (Alpha.encode message.yesterdaysClosingPriceKrx
    ++ (Alpha.encode message.yesterdaysAccumulatedTradingAmount
    ++ (Alpha.encode message.yesterdaysAccumulatedTradingValue
    ++ (Alpha.encode message.upperLimitPrice
    ++ (Alpha.encode message.lowerLimitPrice
    ++ (Alpha.encode message.substitutePriceOfSecurities
    ++ (Alpha.encode message.parValue
    ++ (Alpha.encode message.issuingPrice
    ++ (Alpha.encode message.listingDate
    ++ (Alpha.encode message.numberOfListedShares
    ++ (Alpha.encode message.liquidationTrade
    ++ (Alpha.encode message.theEstablishmentDate
    ++ (Alpha.encode message.maturityDate
    ++ (Alpha.encode message.exercisingPeriod
    ++ (Alpha.encode message.expirationDateForRight
    ++ (Alpha.encode message.exercisePriceOfElwOrBw
    ++ (Alpha.encode message.capital
    ++ (Alpha.encode message.creditOrderPossibility
    ++ (Alpha.encode message.limitOrderPermissionTypeCode
    ++ (Alpha.encode message.marketPriceOrderPermissionTypeCode
    ++ (Alpha.encode message.conditionedOrderPermissionTypeCode
    ++ (Alpha.encode message.bestFavorableOrderPermissionTypeCode
    ++ (Alpha.encode message.firstBestOrderPermissionType
    ++ (Alpha.encode message.midPriceOrderPermissionTypeCode
    ++ (Alpha.encode message.stopLimitPriceOrderPermissionTypeCode
    ++ (Alpha.encode message.capitalIncreaseTypeCode
    ++ (Alpha.encode message.otherStockTypeCode
    ++ (Alpha.encode message.nationalStock
    ++ (Alpha.encode message.appraisedPrice
    ++ (Alpha.encode message.lowestOrderPrice
    ++ (Alpha.encode message.highestOrderPrice
    ++ (Alpha.encode message.unitOfVolumeInMainBoard
    ++ (Alpha.encode message.lotSizeAfterhoursTrading
    ++ (Alpha.encode message.reiTsTypeCode
    ++ (Alpha.encode message.targetStockIsinCode
    ++ (Alpha.encode message.currencyIsoCode
    ++ (Alpha.encode message.countryCode
    ++ (Alpha.encode message.marketMakingPossibility
    ++ (Alpha.encode message.closingPriceTradingPossibilityInTheAfterHours
    ++ (Alpha.encode message.closingPriceTradingInThePreopeningMarket
    ++ (Alpha.encode message.blockTradingInThePreopeningMarket
    ++ (Alpha.encode message.basketTradingInThePreopeningMarket
    ++ (Alpha.encode message.announcementOfEstimatedTradingPrice
    ++ (Alpha.encode message.shortSelling
    ++ (Alpha.encode message.etfTrackingDifference
    ++ (Alpha.encode message.regs
    ++ (Alpha.encode message.spac
    ++ (Alpha.encode message.taxTypeCode
    ++ (Alpha.encode message.appraisalRatioOfSubstitutePrice
    ++ (Alpha.encode message.investmentCautionIssue
    ++ (Alpha.encode message.delistingDate
    ++ (Alpha.encode message.shorttermOverheatIssueTypeCode
    ++ (Alpha.encode message.etfReplicationMethodsTypeCode
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.distributionTypeCode
    ++ (Alpha.encode message.calculationOfRedemptionPriceStartDate
    ++ (Alpha.encode message.calculationOfRedemptionPriceEndDate
    ++ (Alpha.encode message.etpProductTypeCode
    ++ (Alpha.encode message.indexCalculationInstitutionTypeCode
    ++ (Alpha.encode message.indexMarketClassificationId
    ++ (Alpha.encode message.indexSequenceNumber
    ++ (Alpha.encode message.trackingIndexLeverageInverseTypeCode
    ++ (Alpha.encode message.referenceIndexLeverageInverseTypeCode
    ++ (Alpha.encode message.indexAssetClassificationId1
    ++ (Alpha.encode message.indexAssetClassificationId2
    ++ (Alpha.encode message.ipoUnderwriterMemberNumber
    ++ (Alpha.encode message.lpOrder
    ++ (Alpha.encode message.lowLiquidity
    ++ (Alpha.encode message.abnormalRise
    ++ (Alpha.encode message.upperLimitQuantity
    ++ (Alpha.encode message.investmentPrecautionIssue
    ++ (Alpha.encode message.preferredStocksWithLesserShares
    ++ (Alpha.encode message.spacMerger
    ++ (Alpha.encode message.segmentTypeCode
    ++ (Alpha.encode message.afterMarketPossibility
    ++ (Alpha.encode message.choiceOnCompetitiveTrading
    ++ (Alpha.encode message.limitOnCompetitiveTradingVolume
    ++ (Alpha.encode message.occurrenceOfReasonsProhibitingCompetitiveTrading
    ++ (Alpha.encode message.approvalOnCompetitiveTrading
    ++ (Alpha.encode message.approvalOnNegotiationTrading
    ++ (Alpha.encode message.yesterdaysClosingPriceTypeCodeNxt
    ++ (Alpha.encode message.yesterdaysClosingPriceNxt
    ++ (Alpha.encode message.competitionBoardTradePermissionCode
    ++ (Alpha.encode message.negotiationPossibleOrNotBeforeMainMarket
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EquitiesBatchDataMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (totalNumberOfInstrumentsOfTheContract, bytes) ← Alpha.decode 6 bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (abbreviatedIssueCode, bytes) ← Alpha.decode 9 bytes
  let (abbreviatedIssueName, bytes) ← Alpha.decode 40 bytes
  let (abbreviatedIssueNameInEn, bytes) ← Alpha.decode 40 bytes
  let (groupNumber, bytes) ← Alpha.decode 5 bytes
  let (marketOperationProductId, bytes) ← Alpha.decode 3 bytes
  let (securityGroupId, bytes) ← Alpha.decode 2 bytes
  let (unitTrading, bytes) ← Alpha.decode 1 bytes
  let (rightsTypeCode, bytes) ← Alpha.decode 2 bytes
  let (parValueTypeCode, bytes) ← Alpha.decode 2 bytes
  let (anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice, bytes) ← Alpha.decode 1 bytes
  let (reevaluationReasonCode, bytes) ← Alpha.decode 2 bytes
  let (basePriceChange, bytes) ← Alpha.decode 1 bytes
  let (randomEndTriggerCode, bytes) ← Alpha.decode 1 bytes
  let (marketAlert, bytes) ← Alpha.decode 1 bytes
  let (marketAlertTypeCode, bytes) ← Alpha.decode 2 bytes
  let (koreaCorporateGovernanceStockPriceIndexKogi, bytes) ← Alpha.decode 1 bytes
  let (issueForAdministration, bytes) ← Alpha.decode 1 bytes
  let (unfaithfulDisclosure, bytes) ← Alpha.decode 1 bytes
  let (backdoorListing, bytes) ← Alpha.decode 1 bytes
  let (tradingHalt, bytes) ← Alpha.decode 1 bytes
  let (industryId, bytes) ← Alpha.decode 10 bytes
  let (smallMediumSizedBusiness, bytes) ← Alpha.decode 1 bytes
  let (sectionTypeCode, bytes) ← Alpha.decode 1 bytes
  let (investmentInstitutionTypeCode, bytes) ← Alpha.decode 1 bytes
  let (basePrice, bytes) ← Alpha.decode 11 bytes
  let (yesterdaysClosingPriceTypeCodeKrx, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceKrx, bytes) ← Alpha.decode 11 bytes
  let (yesterdaysAccumulatedTradingAmount, bytes) ← Alpha.decode 12 bytes
  let (yesterdaysAccumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (upperLimitPrice, bytes) ← Alpha.decode 11 bytes
  let (lowerLimitPrice, bytes) ← Alpha.decode 11 bytes
  let (substitutePriceOfSecurities, bytes) ← Alpha.decode 11 bytes
  let (parValue, bytes) ← Alpha.decode 11 bytes
  let (issuingPrice, bytes) ← Alpha.decode 11 bytes
  let (listingDate, bytes) ← Alpha.decode 8 bytes
  let (numberOfListedShares, bytes) ← Alpha.decode 16 bytes
  let (liquidationTrade, bytes) ← Alpha.decode 1 bytes
  let (theEstablishmentDate, bytes) ← Alpha.decode 8 bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (exercisingPeriod, bytes) ← Alpha.decode 8 bytes
  let (expirationDateForRight, bytes) ← Alpha.decode 8 bytes
  let (exercisePriceOfElwOrBw, bytes) ← Alpha.decode 13 bytes
  let (capital, bytes) ← Alpha.decode 22 bytes
  let (creditOrderPossibility, bytes) ← Alpha.decode 1 bytes
  let (limitOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (marketPriceOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (conditionedOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (bestFavorableOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (firstBestOrderPermissionType, bytes) ← Alpha.decode 5 bytes
  let (midPriceOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (stopLimitPriceOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (capitalIncreaseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (otherStockTypeCode, bytes) ← Alpha.decode 1 bytes
  let (nationalStock, bytes) ← Alpha.decode 1 bytes
  let (appraisedPrice, bytes) ← Alpha.decode 11 bytes
  let (lowestOrderPrice, bytes) ← Alpha.decode 11 bytes
  let (highestOrderPrice, bytes) ← Alpha.decode 11 bytes
  let (unitOfVolumeInMainBoard, bytes) ← Alpha.decode 11 bytes
  let (lotSizeAfterhoursTrading, bytes) ← Alpha.decode 11 bytes
  let (reiTsTypeCode, bytes) ← Alpha.decode 1 bytes
  let (targetStockIsinCode, bytes) ← Alpha.decode 12 bytes
  let (currencyIsoCode, bytes) ← Alpha.decode 3 bytes
  let (countryCode, bytes) ← Alpha.decode 3 bytes
  let (marketMakingPossibility, bytes) ← Alpha.decode 1 bytes
  let (closingPriceTradingPossibilityInTheAfterHours, bytes) ← Alpha.decode 1 bytes
  let (closingPriceTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (blockTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (basketTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (announcementOfEstimatedTradingPrice, bytes) ← Alpha.decode 1 bytes
  let (shortSelling, bytes) ← Alpha.decode 1 bytes
  let (etfTrackingDifference, bytes) ← Alpha.decode 13 bytes
  let (regs, bytes) ← Alpha.decode 1 bytes
  let (spac, bytes) ← Alpha.decode 1 bytes
  let (taxTypeCode, bytes) ← Alpha.decode 1 bytes
  let (appraisalRatioOfSubstitutePrice, bytes) ← Alpha.decode 13 bytes
  let (investmentCautionIssue, bytes) ← Alpha.decode 1 bytes
  let (delistingDate, bytes) ← Alpha.decode 8 bytes
  let (shorttermOverheatIssueTypeCode, bytes) ← Alpha.decode 1 bytes
  let (etfReplicationMethodsTypeCode, bytes) ← Alpha.decode 1 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (distributionTypeCode, bytes) ← Alpha.decode 2 bytes
  let (calculationOfRedemptionPriceStartDate, bytes) ← Alpha.decode 8 bytes
  let (calculationOfRedemptionPriceEndDate, bytes) ← Alpha.decode 8 bytes
  let (etpProductTypeCode, bytes) ← Alpha.decode 1 bytes
  let (indexCalculationInstitutionTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexMarketClassificationId, bytes) ← Alpha.decode 6 bytes
  let (indexSequenceNumber, bytes) ← Alpha.decode 3 bytes
  let (trackingIndexLeverageInverseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (referenceIndexLeverageInverseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexAssetClassificationId1, bytes) ← Alpha.decode 6 bytes
  let (indexAssetClassificationId2, bytes) ← Alpha.decode 6 bytes
  let (ipoUnderwriterMemberNumber, bytes) ← Alpha.decode 5 bytes
  let (lpOrder, bytes) ← Alpha.decode 1 bytes
  let (lowLiquidity, bytes) ← Alpha.decode 1 bytes
  let (abnormalRise, bytes) ← Alpha.decode 1 bytes
  let (upperLimitQuantity, bytes) ← Alpha.decode 23 bytes
  let (investmentPrecautionIssue, bytes) ← Alpha.decode 1 bytes
  let (preferredStocksWithLesserShares, bytes) ← Alpha.decode 1 bytes
  let (spacMerger, bytes) ← Alpha.decode 1 bytes
  let (segmentTypeCode, bytes) ← Alpha.decode 1 bytes
  let (afterMarketPossibility, bytes) ← Alpha.decode 1 bytes
  let (choiceOnCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (limitOnCompetitiveTradingVolume, bytes) ← Alpha.decode 1 bytes
  let (occurrenceOfReasonsProhibitingCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (approvalOnCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (approvalOnNegotiationTrading, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceTypeCodeNxt, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceNxt, bytes) ← Alpha.decode 11 bytes
  let (competitionBoardTradePermissionCode, bytes) ← Alpha.decode 5 bytes
  let (negotiationPossibleOrNotBeforeMainMarket, bytes) ← Alpha.decode 1 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, totalNumberOfInstrumentsOfTheContract, businessDate, isinCode, aDesignatedNumberForAnIssueFromKrx, abbreviatedIssueCode, abbreviatedIssueName, abbreviatedIssueNameInEn, groupNumber, marketOperationProductId, securityGroupId, unitTrading, rightsTypeCode, parValueTypeCode, anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice, reevaluationReasonCode, basePriceChange, randomEndTriggerCode, marketAlert, marketAlertTypeCode, koreaCorporateGovernanceStockPriceIndexKogi, issueForAdministration, unfaithfulDisclosure, backdoorListing, tradingHalt, industryId, smallMediumSizedBusiness, sectionTypeCode, investmentInstitutionTypeCode, basePrice, yesterdaysClosingPriceTypeCodeKrx, yesterdaysClosingPriceKrx, yesterdaysAccumulatedTradingAmount, yesterdaysAccumulatedTradingValue, upperLimitPrice, lowerLimitPrice, substitutePriceOfSecurities, parValue, issuingPrice, listingDate, numberOfListedShares, liquidationTrade, theEstablishmentDate, maturityDate, exercisingPeriod, expirationDateForRight, exercisePriceOfElwOrBw, capital, creditOrderPossibility, limitOrderPermissionTypeCode, marketPriceOrderPermissionTypeCode, conditionedOrderPermissionTypeCode, bestFavorableOrderPermissionTypeCode, firstBestOrderPermissionType, midPriceOrderPermissionTypeCode, stopLimitPriceOrderPermissionTypeCode, capitalIncreaseTypeCode, otherStockTypeCode, nationalStock, appraisedPrice, lowestOrderPrice, highestOrderPrice, unitOfVolumeInMainBoard, lotSizeAfterhoursTrading, reiTsTypeCode, targetStockIsinCode, currencyIsoCode, countryCode, marketMakingPossibility, closingPriceTradingPossibilityInTheAfterHours, closingPriceTradingInThePreopeningMarket, blockTradingInThePreopeningMarket, basketTradingInThePreopeningMarket, announcementOfEstimatedTradingPrice, shortSelling, etfTrackingDifference, regs, spac, taxTypeCode, appraisalRatioOfSubstitutePrice, investmentCautionIssue, delistingDate, shorttermOverheatIssueTypeCode, etfReplicationMethodsTypeCode, expirationDate, distributionTypeCode, calculationOfRedemptionPriceStartDate, calculationOfRedemptionPriceEndDate, etpProductTypeCode, indexCalculationInstitutionTypeCode, indexMarketClassificationId, indexSequenceNumber, trackingIndexLeverageInverseTypeCode, referenceIndexLeverageInverseTypeCode, indexAssetClassificationId1, indexAssetClassificationId2, ipoUnderwriterMemberNumber, lpOrder, lowLiquidity, abnormalRise, upperLimitQuantity, investmentPrecautionIssue, preferredStocksWithLesserShares, spacMerger, segmentTypeCode, afterMarketPossibility, choiceOnCompetitiveTrading, limitOnCompetitiveTradingVolume, occurrenceOfReasonsProhibitingCompetitiveTrading, approvalOnCompetitiveTrading, approvalOnNegotiationTrading, yesterdaysClosingPriceTypeCodeNxt, yesterdaysClosingPriceNxt, competitionBoardTradePermissionCode, negotiationPossibleOrNotBeforeMainMarket, endKeyword }, bytes)

@[simp] theorem encode_length (message : EquitiesBatchDataMessage) : (encode message).length = 649 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EquitiesBatchDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EquitiesBatchDataMessage) (rest : List UInt8) :
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

end EquitiesBatchDataMessage

/-- Member Information Message: 202 bytes -/
structure MemberInformationMessage where
  messageSequenceNumber : Alpha 8
  businessDate : Alpha 8
  marketParticipantNumber : Alpha 5
  nameOfAMarketParticipantInKr : Alpha 80
  nameOfAMarketParticipantInEn : Alpha 80
  anAbbreviatedNameOfAMarketParticipantInKr : Alpha 20
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MemberInformationMessage

def encode (message : MemberInformationMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.businessDate
    ++ (Alpha.encode message.marketParticipantNumber
    ++ (Alpha.encode message.nameOfAMarketParticipantInKr
    ++ (Alpha.encode message.nameOfAMarketParticipantInEn
    ++ (Alpha.encode message.anAbbreviatedNameOfAMarketParticipantInKr
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (MemberInformationMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  let (marketParticipantNumber, bytes) ← Alpha.decode 5 bytes
  let (nameOfAMarketParticipantInKr, bytes) ← Alpha.decode 80 bytes
  let (nameOfAMarketParticipantInEn, bytes) ← Alpha.decode 80 bytes
  let (anAbbreviatedNameOfAMarketParticipantInKr, bytes) ← Alpha.decode 20 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, businessDate, marketParticipantNumber, nameOfAMarketParticipantInKr, nameOfAMarketParticipantInEn, anAbbreviatedNameOfAMarketParticipantInKr, endKeyword }, bytes)

@[simp] theorem encode_length (message : MemberInformationMessage) : (encode message).length = 202 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MemberInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MemberInformationMessage) (rest : List UInt8) :
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

end MemberInformationMessage

/-- Issue Event Message: 43 bytes -/
structure IssueEventMessage where
  messageSequenceNumber : Alpha 8
  isinCode : Alpha 12
  eventTypeCode : Alpha 2
  eventReasonCode : Alpha 4
  eventStartDate : Alpha 8
  eventEndDate : Alpha 8
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace IssueEventMessage

def encode (message : IssueEventMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.eventTypeCode
    ++ (Alpha.encode message.eventReasonCode
    ++ (Alpha.encode message.eventStartDate
    ++ (Alpha.encode message.eventEndDate
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (IssueEventMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (eventTypeCode, bytes) ← Alpha.decode 2 bytes
  let (eventReasonCode, bytes) ← Alpha.decode 4 bytes
  let (eventStartDate, bytes) ← Alpha.decode 8 bytes
  let (eventEndDate, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, isinCode, eventTypeCode, eventReasonCode, eventStartDate, eventEndDate, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueEventMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IssueEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueEventMessage) (rest : List UInt8) :
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

end IssueEventMessage

/-- Block Basket Trade Data Message: 55 bytes -/
structure BlockBasketTradeDataMessage where
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace BlockBasketTradeDataMessage

def encode (message : BlockBasketTradeDataMessage) : List UInt8 :=
  Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.endKeyword)))))

def decode (bytes : List UInt8) : Option (BlockBasketTradeDataMessage × List UInt8) := do
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, accumulatedTradingVolume, accumulatedTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : BlockBasketTradeDataMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BlockBasketTradeDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockBasketTradeDataMessage) (rest : List UInt8) :
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

end BlockBasketTradeDataMessage

/-- Investor Activities Per An Issue Eod Message: 91 bytes -/
structure InvestorActivitiesPerAnIssueEodMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  investorCode : Alpha 4
  accumulatedAskTradingVolume : Alpha 12
  accumulatedAskTradingValue : Alpha 22
  accumulatedBidTradingVolume : Alpha 12
  accumulatedBidTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace InvestorActivitiesPerAnIssueEodMessage

def encode (message : InvestorActivitiesPerAnIssueEodMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.investorCode
    ++ (Alpha.encode message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (Alpha.encode message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (Alpha.encode message.endKeyword)))))))

def decode (bytes : List UInt8) : Option (InvestorActivitiesPerAnIssueEodMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (investorCode, bytes) ← Alpha.decode 4 bytes
  let (accumulatedAskTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 22 bytes
  let (accumulatedBidTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, investorCode, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : InvestorActivitiesPerAnIssueEodMessage) : (encode message).length = 91 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InvestorActivitiesPerAnIssueEodMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InvestorActivitiesPerAnIssueEodMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InvestorActivitiesPerAnIssueEodMessage

/-- Short Selling Message: 115 bytes -/
structure ShortSellingMessage where
  isinCode : Alpha 12
  coveredShortSellingTradingVolume : Alpha 12
  coveredShortSellingTradingValue : Alpha 22
  uptickRuleAppliedCoveredShortSellingTradingVolume : Alpha 12
  uptickRuleAppliedCoveredShortSellingTradingValue : Alpha 22
  uptickRuleUnappliedCoveredShortSellingTradingVolume : Alpha 12
  uptickRuleUnappliedCoveredShortSellingTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ShortSellingMessage

def encode (message : ShortSellingMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.coveredShortSellingTradingVolume
    ++ (Alpha.encode message.coveredShortSellingTradingValue
    ++ (Alpha.encode message.uptickRuleAppliedCoveredShortSellingTradingVolume
    ++ (Alpha.encode message.uptickRuleAppliedCoveredShortSellingTradingValue
    ++ (Alpha.encode message.uptickRuleUnappliedCoveredShortSellingTradingVolume
    ++ (Alpha.encode message.uptickRuleUnappliedCoveredShortSellingTradingValue
    ++ (Alpha.encode message.endKeyword)))))))

def decode (bytes : List UInt8) : Option (ShortSellingMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (coveredShortSellingTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (coveredShortSellingTradingValue, bytes) ← Alpha.decode 22 bytes
  let (uptickRuleAppliedCoveredShortSellingTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (uptickRuleAppliedCoveredShortSellingTradingValue, bytes) ← Alpha.decode 22 bytes
  let (uptickRuleUnappliedCoveredShortSellingTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (uptickRuleUnappliedCoveredShortSellingTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, coveredShortSellingTradingVolume, coveredShortSellingTradingValue, uptickRuleAppliedCoveredShortSellingTradingVolume, uptickRuleAppliedCoveredShortSellingTradingValue, uptickRuleUnappliedCoveredShortSellingTradingVolume, uptickRuleUnappliedCoveredShortSellingTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : ShortSellingMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ShortSellingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortSellingMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ShortSellingMessage

/-- Brokers Acitity Information Message: 86 bytes -/
structure BrokersAcitityInformationMessage where
  isinCode : Alpha 12
  memberNumber : Alpha 5
  accumulatedAskTradingVolume : Alpha 12
  accumulatedAskTradingValue : Alpha 22
  accumulatedBidTradingVolume : Alpha 12
  accumulatedBidTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace BrokersAcitityInformationMessage

def encode (message : BrokersAcitityInformationMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.memberNumber
    ++ (Alpha.encode message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (Alpha.encode message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (BrokersAcitityInformationMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (memberNumber, bytes) ← Alpha.decode 5 bytes
  let (accumulatedAskTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 22 bytes
  let (accumulatedBidTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, memberNumber, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : BrokersAcitityInformationMessage) : (encode message).length = 86 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BrokersAcitityInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokersAcitityInformationMessage) (rest : List UInt8) :
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

end BrokersAcitityInformationMessage

/-- Trading Activity By Session Per An Issue Message: 120 bytes -/
structure TradingActivityBySessionPerAnIssueMessage where
  isinCode : Alpha 12
  totalNumberOfTradableIssuesOnCompetitiveTrading : Alpha 5
  premarketAccumulatedTradingVolume : Alpha 12
  premarketAccumulatedTradingValue : Alpha 22
  mainmarketAccumulatedTradingVolume : Alpha 12
  mainmarketAccumulatedTradingValue : Alpha 22
  aftermarketAccumulatedTradingVolume : Alpha 12
  aftermarketAccumulatedTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace TradingActivityBySessionPerAnIssueMessage

def encode (message : TradingActivityBySessionPerAnIssueMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.totalNumberOfTradableIssuesOnCompetitiveTrading
    ++ (Alpha.encode message.premarketAccumulatedTradingVolume
    ++ (Alpha.encode message.premarketAccumulatedTradingValue
    ++ (Alpha.encode message.mainmarketAccumulatedTradingVolume
    ++ (Alpha.encode message.mainmarketAccumulatedTradingValue
    ++ (Alpha.encode message.aftermarketAccumulatedTradingVolume
    ++ (Alpha.encode message.aftermarketAccumulatedTradingValue
    ++ (Alpha.encode message.endKeyword))))))))

def decode (bytes : List UInt8) : Option (TradingActivityBySessionPerAnIssueMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (totalNumberOfTradableIssuesOnCompetitiveTrading, bytes) ← Alpha.decode 5 bytes
  let (premarketAccumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (premarketAccumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (mainmarketAccumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (mainmarketAccumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (aftermarketAccumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (aftermarketAccumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, totalNumberOfTradableIssuesOnCompetitiveTrading, premarketAccumulatedTradingVolume, premarketAccumulatedTradingValue, mainmarketAccumulatedTradingVolume, mainmarketAccumulatedTradingValue, aftermarketAccumulatedTradingVolume, aftermarketAccumulatedTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : TradingActivityBySessionPerAnIssueMessage) : (encode message).length = 120 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TradingActivityBySessionPerAnIssueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActivityBySessionPerAnIssueMessage) (rest : List UInt8) :
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

end TradingActivityBySessionPerAnIssueMessage

/-- Any Payload, selected by TR Code -/
inductive Payload where
  | pollingDataMessage (message : PollingDataMessage) -- "I2500" 0x4932353030
  | securitiesQuote10LevelMessage (message : SecuritiesQuote10LevelMessage) -- "B651S" 0x4236353153
  | securitiesQuote10LevelMessage284377297233 (message : SecuritiesQuote10LevelMessage) -- "B651Q" 0x4236353151
  | securitiesOrderFilledMessage (message : SecuritiesOrderFilledMessage) -- "A351S" 0x4133353153
  | securitiesOrderFilledMessage280031998289 (message : SecuritiesOrderFilledMessage) -- "A351Q" 0x4133353151
  | marketOperationTsMessage (message : MarketOperationTsMessage) -- "A751S" 0x4137353153
  | marketOperationTsMessage280099107153 (message : MarketOperationTsMessage) -- "A751Q" 0x4137353151
  | issueClosingMessage (message : IssueClosingMessage) -- "A651S" 0x4136353153
  | issueClosingMessage280082329937 (message : IssueClosingMessage) -- "A651Q" 0x4136353151
  | triggeringRemovingViMessage (message : TriggeringRemovingViMessage) -- "R851S" 0x5238353153
  | triggeringRemovingViMessage353130328401 (message : TriggeringRemovingViMessage) -- "R851Q" 0x5238353151
  | closingPriceTradingQuoteMessage (message : ClosingPriceTradingQuoteMessage) -- "E151S" 0x4531353153
  | closingPriceTradingQuoteMessage297178313041 (message : ClosingPriceTradingQuoteMessage) -- "E151Q" 0x4531353151
  | equitiesSnapshot10LevelMessage (message : EquitiesSnapshot10LevelMessage) -- "B251S" 0x4232353153
  | equitiesSnapshot10LevelMessage284310188369 (message : EquitiesSnapshot10LevelMessage) -- "B251Q" 0x4232353151
  | investorActivitiesPerAnIndustryMessage (message : InvestorActivitiesPerAnIndustryMessage) -- "C051S" 0x4330353153
  | investorActivitiesPerAnIndustryMessage288571601233 (message : InvestorActivitiesPerAnIndustryMessage) -- "C051Q" 0x4330353151
  | currentMovementMessage (message : CurrentMovementMessage) -- "B551S" 0x4235353153
  | currentMovementMessage284360520017 (message : CurrentMovementMessage) -- "B551Q" 0x4235353151
  | programTradingActivityPerInvestorMessage (message : ProgramTradingActivityPerInvestorMessage) -- "P051S" 0x5030353153
  | programTradingActivityPerInvestorMessage344406176081 (message : ProgramTradingActivityPerInvestorMessage) -- "P051Q" 0x5030353151
  | programTradingInformationPerIssueAggregatedInformationMessage (message : ProgramTradingInformationPerIssueAggregatedInformationMessage) -- "C351S" 0x4333353153
  | programTradingInformationPerIssueAggregatedInformationMessage288621932881 (message : ProgramTradingInformationPerIssueAggregatedInformationMessage) -- "C351Q" 0x4333353151
  | programTradingInformationOfTotalAggregatedInformationMessage (message : ProgramTradingInformationOfTotalAggregatedInformationMessage) -- "J051S" 0x4A30353153
  | programTradingInformationOfTotalAggregatedInformationMessage318636372305 (message : ProgramTradingInformationOfTotalAggregatedInformationMessage) -- "J051Q" 0x4A30353151
  | marketOperationScheduleMessage (message : MarketOperationScheduleMessage) -- "M451S" 0x4D34353153
  | marketOperationScheduleMessage331588383057 (message : MarketOperationScheduleMessage) -- "M451Q" 0x4D34353151
  | memberFirmImposingLiftingSanctionsMessage (message : MemberFirmImposingLiftingSanctionsMessage) -- "R351T" 0x5233353154
  | topFiveTradersActivitiesMessage (message : TopFiveTradersActivitiesMessage) -- "B951S" 0x4239353153
  | topFiveTradersActivitiesMessage284427628881 (message : TopFiveTradersActivitiesMessage) -- "B951Q" 0x4239353151
  | equitiesBatchDataMessage (message : EquitiesBatchDataMessage) -- "A051S" 0x4130353153
  | equitiesBatchDataMessage297161535827 (message : EquitiesBatchDataMessage) -- "E051S" 0x4530353153
  | equitiesBatchDataMessage279981666641 (message : EquitiesBatchDataMessage) -- "A051Q" 0x4130353151
  | equitiesBatchDataMessage297161535825 (message : EquitiesBatchDataMessage) -- "E051Q" 0x4530353151
  | memberInformationMessage (message : MemberInformationMessage) -- "M951T" 0x4D39353154
  | memberInformationMessage297295753556 (message : MemberInformationMessage) -- "E851T" 0x4538353154
  | issueEventMessage (message : IssueEventMessage) -- "I651S" 0x4936353153
  | issueEventMessage297262199123 (message : IssueEventMessage) -- "E651S" 0x4536353153
  | issueEventMessage314442068305 (message : IssueEventMessage) -- "I651Q" 0x4936353151
  | issueEventMessage297262199121 (message : IssueEventMessage) -- "E651Q" 0x4536353151
  | blockBasketTradeDataMessage (message : BlockBasketTradeDataMessage) -- "C451S" 0x4334353153
  | blockBasketTradeDataMessage288638710097 (message : BlockBasketTradeDataMessage) -- "C451Q" 0x4334353151
  | investorActivitiesPerAnIssueEodMessage (message : InvestorActivitiesPerAnIssueEodMessage) -- "C151S" 0x4331353153
  | investorActivitiesPerAnIssueEodMessage288588378449 (message : InvestorActivitiesPerAnIssueEodMessage) -- "C151Q" 0x4331353151
  | shortSellingMessage (message : ShortSellingMessage) -- "I851S" 0x4938353153
  | shortSellingMessage314475622737 (message : ShortSellingMessage) -- "I851Q" 0x4938353151
  | brokersAcitityInformationMessage (message : BrokersAcitityInformationMessage) -- "E251S" 0x4532353153
  | brokersAcitityInformationMessage297195090257 (message : BrokersAcitityInformationMessage) -- "E251Q" 0x4532353151
  | tradingActivityBySessionPerAnIssueMessage (message : TradingActivityBySessionPerAnIssueMessage) -- "E351S" 0x4533353153
  | tradingActivityBySessionPerAnIssueMessage297211867473 (message : TradingActivityBySessionPerAnIssueMessage) -- "E351Q" 0x4533353151
  deriving DecidableEq, Repr

namespace Payload

/-- The TR Code each message is sent under -/
def tag : Payload → BitVec 40
  | .pollingDataMessage _ => 314374959152
  | .securitiesQuote10LevelMessage _ => 284377297235
  | .securitiesQuote10LevelMessage284377297233 _ => 284377297233
  | .securitiesOrderFilledMessage _ => 280031998291
  | .securitiesOrderFilledMessage280031998289 _ => 280031998289
  | .marketOperationTsMessage _ => 280099107155
  | .marketOperationTsMessage280099107153 _ => 280099107153
  | .issueClosingMessage _ => 280082329939
  | .issueClosingMessage280082329937 _ => 280082329937
  | .triggeringRemovingViMessage _ => 353130328403
  | .triggeringRemovingViMessage353130328401 _ => 353130328401
  | .closingPriceTradingQuoteMessage _ => 297178313043
  | .closingPriceTradingQuoteMessage297178313041 _ => 297178313041
  | .equitiesSnapshot10LevelMessage _ => 284310188371
  | .equitiesSnapshot10LevelMessage284310188369 _ => 284310188369
  | .investorActivitiesPerAnIndustryMessage _ => 288571601235
  | .investorActivitiesPerAnIndustryMessage288571601233 _ => 288571601233
  | .currentMovementMessage _ => 284360520019
  | .currentMovementMessage284360520017 _ => 284360520017
  | .programTradingActivityPerInvestorMessage _ => 344406176083
  | .programTradingActivityPerInvestorMessage344406176081 _ => 344406176081
  | .programTradingInformationPerIssueAggregatedInformationMessage _ => 288621932883
  | .programTradingInformationPerIssueAggregatedInformationMessage288621932881 _ => 288621932881
  | .programTradingInformationOfTotalAggregatedInformationMessage _ => 318636372307
  | .programTradingInformationOfTotalAggregatedInformationMessage318636372305 _ => 318636372305
  | .marketOperationScheduleMessage _ => 331588383059
  | .marketOperationScheduleMessage331588383057 _ => 331588383057
  | .memberFirmImposingLiftingSanctionsMessage _ => 353046442324
  | .topFiveTradersActivitiesMessage _ => 284427628883
  | .topFiveTradersActivitiesMessage284427628881 _ => 284427628881
  | .equitiesBatchDataMessage _ => 279981666643
  | .equitiesBatchDataMessage297161535827 _ => 297161535827
  | .equitiesBatchDataMessage279981666641 _ => 279981666641
  | .equitiesBatchDataMessage297161535825 _ => 297161535825
  | .memberInformationMessage _ => 331672269140
  | .memberInformationMessage297295753556 _ => 297295753556
  | .issueEventMessage _ => 314442068307
  | .issueEventMessage297262199123 _ => 297262199123
  | .issueEventMessage314442068305 _ => 314442068305
  | .issueEventMessage297262199121 _ => 297262199121
  | .blockBasketTradeDataMessage _ => 288638710099
  | .blockBasketTradeDataMessage288638710097 _ => 288638710097
  | .investorActivitiesPerAnIssueEodMessage _ => 288588378451
  | .investorActivitiesPerAnIssueEodMessage288588378449 _ => 288588378449
  | .shortSellingMessage _ => 314475622739
  | .shortSellingMessage314475622737 _ => 314475622737
  | .brokersAcitityInformationMessage _ => 297195090259
  | .brokersAcitityInformationMessage297195090257 _ => 297195090257
  | .tradingActivityBySessionPerAnIssueMessage _ => 297211867475
  | .tradingActivityBySessionPerAnIssueMessage297211867473 _ => 297211867473

def encode : Payload → List UInt8
  | .pollingDataMessage message => PollingDataMessage.encode message
  | .securitiesQuote10LevelMessage message => SecuritiesQuote10LevelMessage.encode message
  | .securitiesQuote10LevelMessage284377297233 message => SecuritiesQuote10LevelMessage.encode message
  | .securitiesOrderFilledMessage message => SecuritiesOrderFilledMessage.encode message
  | .securitiesOrderFilledMessage280031998289 message => SecuritiesOrderFilledMessage.encode message
  | .marketOperationTsMessage message => MarketOperationTsMessage.encode message
  | .marketOperationTsMessage280099107153 message => MarketOperationTsMessage.encode message
  | .issueClosingMessage message => IssueClosingMessage.encode message
  | .issueClosingMessage280082329937 message => IssueClosingMessage.encode message
  | .triggeringRemovingViMessage message => TriggeringRemovingViMessage.encode message
  | .triggeringRemovingViMessage353130328401 message => TriggeringRemovingViMessage.encode message
  | .closingPriceTradingQuoteMessage message => ClosingPriceTradingQuoteMessage.encode message
  | .closingPriceTradingQuoteMessage297178313041 message => ClosingPriceTradingQuoteMessage.encode message
  | .equitiesSnapshot10LevelMessage message => EquitiesSnapshot10LevelMessage.encode message
  | .equitiesSnapshot10LevelMessage284310188369 message => EquitiesSnapshot10LevelMessage.encode message
  | .investorActivitiesPerAnIndustryMessage message => InvestorActivitiesPerAnIndustryMessage.encode message
  | .investorActivitiesPerAnIndustryMessage288571601233 message => InvestorActivitiesPerAnIndustryMessage.encode message
  | .currentMovementMessage message => CurrentMovementMessage.encode message
  | .currentMovementMessage284360520017 message => CurrentMovementMessage.encode message
  | .programTradingActivityPerInvestorMessage message => ProgramTradingActivityPerInvestorMessage.encode message
  | .programTradingActivityPerInvestorMessage344406176081 message => ProgramTradingActivityPerInvestorMessage.encode message
  | .programTradingInformationPerIssueAggregatedInformationMessage message => ProgramTradingInformationPerIssueAggregatedInformationMessage.encode message
  | .programTradingInformationPerIssueAggregatedInformationMessage288621932881 message => ProgramTradingInformationPerIssueAggregatedInformationMessage.encode message
  | .programTradingInformationOfTotalAggregatedInformationMessage message => ProgramTradingInformationOfTotalAggregatedInformationMessage.encode message
  | .programTradingInformationOfTotalAggregatedInformationMessage318636372305 message => ProgramTradingInformationOfTotalAggregatedInformationMessage.encode message
  | .marketOperationScheduleMessage message => MarketOperationScheduleMessage.encode message
  | .marketOperationScheduleMessage331588383057 message => MarketOperationScheduleMessage.encode message
  | .memberFirmImposingLiftingSanctionsMessage message => MemberFirmImposingLiftingSanctionsMessage.encode message
  | .topFiveTradersActivitiesMessage message => TopFiveTradersActivitiesMessage.encode message
  | .topFiveTradersActivitiesMessage284427628881 message => TopFiveTradersActivitiesMessage.encode message
  | .equitiesBatchDataMessage message => EquitiesBatchDataMessage.encode message
  | .equitiesBatchDataMessage297161535827 message => EquitiesBatchDataMessage.encode message
  | .equitiesBatchDataMessage279981666641 message => EquitiesBatchDataMessage.encode message
  | .equitiesBatchDataMessage297161535825 message => EquitiesBatchDataMessage.encode message
  | .memberInformationMessage message => MemberInformationMessage.encode message
  | .memberInformationMessage297295753556 message => MemberInformationMessage.encode message
  | .issueEventMessage message => IssueEventMessage.encode message
  | .issueEventMessage297262199123 message => IssueEventMessage.encode message
  | .issueEventMessage314442068305 message => IssueEventMessage.encode message
  | .issueEventMessage297262199121 message => IssueEventMessage.encode message
  | .blockBasketTradeDataMessage message => BlockBasketTradeDataMessage.encode message
  | .blockBasketTradeDataMessage288638710097 message => BlockBasketTradeDataMessage.encode message
  | .investorActivitiesPerAnIssueEodMessage message => InvestorActivitiesPerAnIssueEodMessage.encode message
  | .investorActivitiesPerAnIssueEodMessage288588378449 message => InvestorActivitiesPerAnIssueEodMessage.encode message
  | .shortSellingMessage message => ShortSellingMessage.encode message
  | .shortSellingMessage314475622737 message => ShortSellingMessage.encode message
  | .brokersAcitityInformationMessage message => BrokersAcitityInformationMessage.encode message
  | .brokersAcitityInformationMessage297195090257 message => BrokersAcitityInformationMessage.encode message
  | .tradingActivityBySessionPerAnIssueMessage message => TradingActivityBySessionPerAnIssueMessage.encode message
  | .tradingActivityBySessionPerAnIssueMessage297211867473 message => TradingActivityBySessionPerAnIssueMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 680 := by
  cases message with
  | pollingDataMessage inner =>
    simp only [encode, PollingDataMessage.encode_length]
    omega
  | securitiesQuote10LevelMessage inner =>
    simp only [encode, SecuritiesQuote10LevelMessage.encode_length]
    omega
  | securitiesQuote10LevelMessage284377297233 inner =>
    simp only [encode, SecuritiesQuote10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | securitiesOrderFilledMessage280031998289 inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | marketOperationTsMessage280099107153 inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | issueClosingMessage280082329937 inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | triggeringRemovingViMessage353130328401 inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage297178313041 inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | equitiesSnapshot10LevelMessage inner =>
    simp only [encode, EquitiesSnapshot10LevelMessage.encode_length]
    omega
  | equitiesSnapshot10LevelMessage284310188369 inner =>
    simp only [encode, EquitiesSnapshot10LevelMessage.encode_length]
    omega
  | investorActivitiesPerAnIndustryMessage inner =>
    simp only [encode, InvestorActivitiesPerAnIndustryMessage.encode_length]
    omega
  | investorActivitiesPerAnIndustryMessage288571601233 inner =>
    simp only [encode, InvestorActivitiesPerAnIndustryMessage.encode_length]
    omega
  | currentMovementMessage inner =>
    simp only [encode, CurrentMovementMessage.encode_length]
    omega
  | currentMovementMessage284360520017 inner =>
    simp only [encode, CurrentMovementMessage.encode_length]
    omega
  | programTradingActivityPerInvestorMessage inner =>
    simp only [encode, ProgramTradingActivityPerInvestorMessage.encode_length]
    omega
  | programTradingActivityPerInvestorMessage344406176081 inner =>
    simp only [encode, ProgramTradingActivityPerInvestorMessage.encode_length]
    omega
  | programTradingInformationPerIssueAggregatedInformationMessage inner =>
    simp only [encode, ProgramTradingInformationPerIssueAggregatedInformationMessage.encode_length]
    omega
  | programTradingInformationPerIssueAggregatedInformationMessage288621932881 inner =>
    simp only [encode, ProgramTradingInformationPerIssueAggregatedInformationMessage.encode_length]
    omega
  | programTradingInformationOfTotalAggregatedInformationMessage inner =>
    simp only [encode, ProgramTradingInformationOfTotalAggregatedInformationMessage.encode_length]
    omega
  | programTradingInformationOfTotalAggregatedInformationMessage318636372305 inner =>
    simp only [encode, ProgramTradingInformationOfTotalAggregatedInformationMessage.encode_length]
    omega
  | marketOperationScheduleMessage inner =>
    simp only [encode, MarketOperationScheduleMessage.encode_length]
    omega
  | marketOperationScheduleMessage331588383057 inner =>
    simp only [encode, MarketOperationScheduleMessage.encode_length]
    omega
  | memberFirmImposingLiftingSanctionsMessage inner =>
    simp only [encode, MemberFirmImposingLiftingSanctionsMessage.encode_length]
    omega
  | topFiveTradersActivitiesMessage inner =>
    simp only [encode, TopFiveTradersActivitiesMessage.encode_length]
    omega
  | topFiveTradersActivitiesMessage284427628881 inner =>
    simp only [encode, TopFiveTradersActivitiesMessage.encode_length]
    omega
  | equitiesBatchDataMessage inner =>
    simp only [encode, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage297161535827 inner =>
    simp only [encode, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage279981666641 inner =>
    simp only [encode, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage297161535825 inner =>
    simp only [encode, EquitiesBatchDataMessage.encode_length]
    omega
  | memberInformationMessage inner =>
    simp only [encode, MemberInformationMessage.encode_length]
    omega
  | memberInformationMessage297295753556 inner =>
    simp only [encode, MemberInformationMessage.encode_length]
    omega
  | issueEventMessage inner =>
    simp only [encode, IssueEventMessage.encode_length]
    omega
  | issueEventMessage297262199123 inner =>
    simp only [encode, IssueEventMessage.encode_length]
    omega
  | issueEventMessage314442068305 inner =>
    simp only [encode, IssueEventMessage.encode_length]
    omega
  | issueEventMessage297262199121 inner =>
    simp only [encode, IssueEventMessage.encode_length]
    omega
  | blockBasketTradeDataMessage inner =>
    simp only [encode, BlockBasketTradeDataMessage.encode_length]
    omega
  | blockBasketTradeDataMessage288638710097 inner =>
    simp only [encode, BlockBasketTradeDataMessage.encode_length]
    omega
  | investorActivitiesPerAnIssueEodMessage inner =>
    simp only [encode, InvestorActivitiesPerAnIssueEodMessage.encode_length]
    omega
  | investorActivitiesPerAnIssueEodMessage288588378449 inner =>
    simp only [encode, InvestorActivitiesPerAnIssueEodMessage.encode_length]
    omega
  | shortSellingMessage inner =>
    simp only [encode, ShortSellingMessage.encode_length]
    omega
  | shortSellingMessage314475622737 inner =>
    simp only [encode, ShortSellingMessage.encode_length]
    omega
  | brokersAcitityInformationMessage inner =>
    simp only [encode, BrokersAcitityInformationMessage.encode_length]
    omega
  | brokersAcitityInformationMessage297195090257 inner =>
    simp only [encode, BrokersAcitityInformationMessage.encode_length]
    omega
  | tradingActivityBySessionPerAnIssueMessage inner =>
    simp only [encode, TradingActivityBySessionPerAnIssueMessage.encode_length]
    omega
  | tradingActivityBySessionPerAnIssueMessage297211867473 inner =>
    simp only [encode, TradingActivityBySessionPerAnIssueMessage.encode_length]
    omega

def decode (tag : BitVec 40) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 314374959152 then (PollingDataMessage.decode bytes).map fun (message, rest) => (.pollingDataMessage message, rest)
  else if tag = 284377297235 then (SecuritiesQuote10LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuote10LevelMessage message, rest)
  else if tag = 284377297233 then (SecuritiesQuote10LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuote10LevelMessage284377297233 message, rest)
  else if tag = 280031998291 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage message, rest)
  else if tag = 280031998289 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage280031998289 message, rest)
  else if tag = 280099107155 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage message, rest)
  else if tag = 280099107153 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage280099107153 message, rest)
  else if tag = 280082329939 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage message, rest)
  else if tag = 280082329937 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage280082329937 message, rest)
  else if tag = 353130328403 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage message, rest)
  else if tag = 353130328401 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage353130328401 message, rest)
  else if tag = 297178313043 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage message, rest)
  else if tag = 297178313041 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage297178313041 message, rest)
  else if tag = 284310188371 then (EquitiesSnapshot10LevelMessage.decode bytes).map fun (message, rest) => (.equitiesSnapshot10LevelMessage message, rest)
  else if tag = 284310188369 then (EquitiesSnapshot10LevelMessage.decode bytes).map fun (message, rest) => (.equitiesSnapshot10LevelMessage284310188369 message, rest)
  else if tag = 288571601235 then (InvestorActivitiesPerAnIndustryMessage.decode bytes).map fun (message, rest) => (.investorActivitiesPerAnIndustryMessage message, rest)
  else if tag = 288571601233 then (InvestorActivitiesPerAnIndustryMessage.decode bytes).map fun (message, rest) => (.investorActivitiesPerAnIndustryMessage288571601233 message, rest)
  else if tag = 284360520019 then (CurrentMovementMessage.decode bytes).map fun (message, rest) => (.currentMovementMessage message, rest)
  else if tag = 284360520017 then (CurrentMovementMessage.decode bytes).map fun (message, rest) => (.currentMovementMessage284360520017 message, rest)
  else if tag = 344406176083 then (ProgramTradingActivityPerInvestorMessage.decode bytes).map fun (message, rest) => (.programTradingActivityPerInvestorMessage message, rest)
  else if tag = 344406176081 then (ProgramTradingActivityPerInvestorMessage.decode bytes).map fun (message, rest) => (.programTradingActivityPerInvestorMessage344406176081 message, rest)
  else if tag = 288621932883 then (ProgramTradingInformationPerIssueAggregatedInformationMessage.decode bytes).map fun (message, rest) => (.programTradingInformationPerIssueAggregatedInformationMessage message, rest)
  else if tag = 288621932881 then (ProgramTradingInformationPerIssueAggregatedInformationMessage.decode bytes).map fun (message, rest) => (.programTradingInformationPerIssueAggregatedInformationMessage288621932881 message, rest)
  else if tag = 318636372307 then (ProgramTradingInformationOfTotalAggregatedInformationMessage.decode bytes).map fun (message, rest) => (.programTradingInformationOfTotalAggregatedInformationMessage message, rest)
  else if tag = 318636372305 then (ProgramTradingInformationOfTotalAggregatedInformationMessage.decode bytes).map fun (message, rest) => (.programTradingInformationOfTotalAggregatedInformationMessage318636372305 message, rest)
  else if tag = 331588383059 then (MarketOperationScheduleMessage.decode bytes).map fun (message, rest) => (.marketOperationScheduleMessage message, rest)
  else if tag = 331588383057 then (MarketOperationScheduleMessage.decode bytes).map fun (message, rest) => (.marketOperationScheduleMessage331588383057 message, rest)
  else if tag = 353046442324 then (MemberFirmImposingLiftingSanctionsMessage.decode bytes).map fun (message, rest) => (.memberFirmImposingLiftingSanctionsMessage message, rest)
  else if tag = 284427628883 then (TopFiveTradersActivitiesMessage.decode bytes).map fun (message, rest) => (.topFiveTradersActivitiesMessage message, rest)
  else if tag = 284427628881 then (TopFiveTradersActivitiesMessage.decode bytes).map fun (message, rest) => (.topFiveTradersActivitiesMessage284427628881 message, rest)
  else if tag = 279981666643 then (EquitiesBatchDataMessage.decode bytes).map fun (message, rest) => (.equitiesBatchDataMessage message, rest)
  else if tag = 297161535827 then (EquitiesBatchDataMessage.decode bytes).map fun (message, rest) => (.equitiesBatchDataMessage297161535827 message, rest)
  else if tag = 279981666641 then (EquitiesBatchDataMessage.decode bytes).map fun (message, rest) => (.equitiesBatchDataMessage279981666641 message, rest)
  else if tag = 297161535825 then (EquitiesBatchDataMessage.decode bytes).map fun (message, rest) => (.equitiesBatchDataMessage297161535825 message, rest)
  else if tag = 331672269140 then (MemberInformationMessage.decode bytes).map fun (message, rest) => (.memberInformationMessage message, rest)
  else if tag = 297295753556 then (MemberInformationMessage.decode bytes).map fun (message, rest) => (.memberInformationMessage297295753556 message, rest)
  else if tag = 314442068307 then (IssueEventMessage.decode bytes).map fun (message, rest) => (.issueEventMessage message, rest)
  else if tag = 297262199123 then (IssueEventMessage.decode bytes).map fun (message, rest) => (.issueEventMessage297262199123 message, rest)
  else if tag = 314442068305 then (IssueEventMessage.decode bytes).map fun (message, rest) => (.issueEventMessage314442068305 message, rest)
  else if tag = 297262199121 then (IssueEventMessage.decode bytes).map fun (message, rest) => (.issueEventMessage297262199121 message, rest)
  else if tag = 288638710099 then (BlockBasketTradeDataMessage.decode bytes).map fun (message, rest) => (.blockBasketTradeDataMessage message, rest)
  else if tag = 288638710097 then (BlockBasketTradeDataMessage.decode bytes).map fun (message, rest) => (.blockBasketTradeDataMessage288638710097 message, rest)
  else if tag = 288588378451 then (InvestorActivitiesPerAnIssueEodMessage.decode bytes).map fun (message, rest) => (.investorActivitiesPerAnIssueEodMessage message, rest)
  else if tag = 288588378449 then (InvestorActivitiesPerAnIssueEodMessage.decode bytes).map fun (message, rest) => (.investorActivitiesPerAnIssueEodMessage288588378449 message, rest)
  else if tag = 314475622739 then (ShortSellingMessage.decode bytes).map fun (message, rest) => (.shortSellingMessage message, rest)
  else if tag = 314475622737 then (ShortSellingMessage.decode bytes).map fun (message, rest) => (.shortSellingMessage314475622737 message, rest)
  else if tag = 297195090259 then (BrokersAcitityInformationMessage.decode bytes).map fun (message, rest) => (.brokersAcitityInformationMessage message, rest)
  else if tag = 297195090257 then (BrokersAcitityInformationMessage.decode bytes).map fun (message, rest) => (.brokersAcitityInformationMessage297195090257 message, rest)
  else if tag = 297211867475 then (TradingActivityBySessionPerAnIssueMessage.decode bytes).map fun (message, rest) => (.tradingActivityBySessionPerAnIssueMessage message, rest)
  else if tag = 297211867473 then (TradingActivityBySessionPerAnIssueMessage.decode bytes).map fun (message, rest) => (.tradingActivityBySessionPerAnIssueMessage297211867473 message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  payload : Payload
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 5 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (trCode, bytes) ← decodeUInt 5 bytes
  let (payload, bytes) ← Payload.decode trCode bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 685 := by
  unfold encode
  cases message.payload with
  | pollingDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PollingDataMessage.encode_length]
    omega
  | securitiesQuote10LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuote10LevelMessage.encode_length]
    omega
  | securitiesQuote10LevelMessage284377297233 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuote10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | securitiesOrderFilledMessage280031998289 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | marketOperationTsMessage280099107153 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | issueClosingMessage280082329937 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | triggeringRemovingViMessage353130328401 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage297178313041 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | equitiesSnapshot10LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesSnapshot10LevelMessage.encode_length]
    omega
  | equitiesSnapshot10LevelMessage284310188369 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesSnapshot10LevelMessage.encode_length]
    omega
  | investorActivitiesPerAnIndustryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InvestorActivitiesPerAnIndustryMessage.encode_length]
    omega
  | investorActivitiesPerAnIndustryMessage288571601233 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InvestorActivitiesPerAnIndustryMessage.encode_length]
    omega
  | currentMovementMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CurrentMovementMessage.encode_length]
    omega
  | currentMovementMessage284360520017 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CurrentMovementMessage.encode_length]
    omega
  | programTradingActivityPerInvestorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProgramTradingActivityPerInvestorMessage.encode_length]
    omega
  | programTradingActivityPerInvestorMessage344406176081 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProgramTradingActivityPerInvestorMessage.encode_length]
    omega
  | programTradingInformationPerIssueAggregatedInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProgramTradingInformationPerIssueAggregatedInformationMessage.encode_length]
    omega
  | programTradingInformationPerIssueAggregatedInformationMessage288621932881 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProgramTradingInformationPerIssueAggregatedInformationMessage.encode_length]
    omega
  | programTradingInformationOfTotalAggregatedInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProgramTradingInformationOfTotalAggregatedInformationMessage.encode_length]
    omega
  | programTradingInformationOfTotalAggregatedInformationMessage318636372305 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProgramTradingInformationOfTotalAggregatedInformationMessage.encode_length]
    omega
  | marketOperationScheduleMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationScheduleMessage.encode_length]
    omega
  | marketOperationScheduleMessage331588383057 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationScheduleMessage.encode_length]
    omega
  | memberFirmImposingLiftingSanctionsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberFirmImposingLiftingSanctionsMessage.encode_length]
    omega
  | topFiveTradersActivitiesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopFiveTradersActivitiesMessage.encode_length]
    omega
  | topFiveTradersActivitiesMessage284427628881 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopFiveTradersActivitiesMessage.encode_length]
    omega
  | equitiesBatchDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage297161535827 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage279981666641 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage297161535825 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesBatchDataMessage.encode_length]
    omega
  | memberInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberInformationMessage.encode_length]
    omega
  | memberInformationMessage297295753556 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberInformationMessage.encode_length]
    omega
  | issueEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueEventMessage.encode_length]
    omega
  | issueEventMessage297262199123 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueEventMessage.encode_length]
    omega
  | issueEventMessage314442068305 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueEventMessage.encode_length]
    omega
  | issueEventMessage297262199121 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueEventMessage.encode_length]
    omega
  | blockBasketTradeDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BlockBasketTradeDataMessage.encode_length]
    omega
  | blockBasketTradeDataMessage288638710097 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BlockBasketTradeDataMessage.encode_length]
    omega
  | investorActivitiesPerAnIssueEodMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InvestorActivitiesPerAnIssueEodMessage.encode_length]
    omega
  | investorActivitiesPerAnIssueEodMessage288588378449 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InvestorActivitiesPerAnIssueEodMessage.encode_length]
    omega
  | shortSellingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortSellingMessage.encode_length]
    omega
  | shortSellingMessage314475622737 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortSellingMessage.encode_length]
    omega
  | brokersAcitityInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokersAcitityInformationMessage.encode_length]
    omega
  | brokersAcitityInformationMessage297195090257 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokersAcitityInformationMessage.encode_length]
    omega
  | tradingActivityBySessionPerAnIssueMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActivityBySessionPerAnIssueMessage.encode_length]
    omega
  | tradingActivityBySessionPerAnIssueMessage297211867473 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActivityBySessionPerAnIssueMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Packet

end Omi.NextradeNextradeStockcommonNxtasciiV212
