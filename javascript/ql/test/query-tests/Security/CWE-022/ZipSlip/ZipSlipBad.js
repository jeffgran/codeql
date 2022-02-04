const fs = require('fs');
const unzip = require('unzip');

fs.createReadStream('archive.zip')
  .pipe(unzip.Parse())
  .on('entry', entry => {
    const fileName = entry.path;
    entry.pipe(fs.createWriteStream(fileName));
  });

var Writer = require('fstream').Writer;
fs.createReadStream('archive.zip')
  .pipe(unzip.Parse())
  .on('entry', entry => {
    const fileName = entry.path;
    entry.pipe(Writer({path: fileName}));
  });

fs.createReadStream('archive.zip')
  .pipe(unzip.Parse())
  .on('entry', entry => {
    const fileName = entry.path;
    var file = fs.openSync(fileName, "w");
  });

const JSZip = require('jszip');
const zip = new JSZip();
function doZipSlip() {
  for (const name in zip.files) {
    fs.createWriteStream(name);
  }

  zip.forEach((name, file) => {
    fs.createWriteStream(name);
  });
}