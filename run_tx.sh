inputPath=$1
outputPath=$2

if [ ! -e "$inputPath" ]
then
  echo "inputPath exist!"
  return
fi

if [ -e "$outputPath" ]
then
  rm -rf "$outputPath"
  mkdir "$outputPath"
else
  mkdir "$outputPath"
fi

for file in `ls "$inputPath" -v *.c`
do
  if [ -f "$file" ]
  then
    mkdir "$outputPath"/"$file"
    cp "$file" "$outputPath"/"$file"/"$file"
    TestCaseGenerate "$outputPath"/"$file"/"$file" -MCC -condition -decision -CDC -MCDC -kappa-mode=a -ignore-printf -addI=false -addD=false -all-func-expect-main --

  fi
done