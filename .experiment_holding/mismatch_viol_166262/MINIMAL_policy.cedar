forbid(principal, action == Action::"d", resource) when {
  (({b: resource, k: true}.b).hasTag("owner")) && (({b: resource, k: true}.b).getTag("owner"))
};
