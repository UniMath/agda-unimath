document.addEventListener('DOMContentLoaded', (event) => {
  if (window.location.href.includes("/redirect/goatcounter")) {
    window.location.href = 'https://agda-unimath.goatcounter.com/count';
  }
});
