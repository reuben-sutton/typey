# typed: true

def rescue_local_is_nil_before_rescue
  begin
  rescue StandardError => exception
    error = exception
  end

  T.reveal_type(error) # note: NilClass
end
