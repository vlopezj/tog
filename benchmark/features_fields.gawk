match($0, /field_[a-z]*\("([A-Za-z_-]+)"/, data) && !uniq[data[1]]++ { print data[1] }