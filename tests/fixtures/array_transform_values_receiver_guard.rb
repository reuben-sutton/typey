# typed: true

values = [1, 2, 3]
values.transform_values { |value| value.to_s } # error: transform_values
