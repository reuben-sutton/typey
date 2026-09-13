class Date
  def to_time(form = :local)
    Time.new
  end
end

T.reveal_type(Date.new.to_time(:utc)) # note: Revealed type: `Time`
