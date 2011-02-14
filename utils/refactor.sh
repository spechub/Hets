for i in TERM FORMULA
 do
  find . -name "*.hs" -exec sed -i 's/\([^a-zA-Z]\)$$i f/\1$$i t f/g' {} \;
done

