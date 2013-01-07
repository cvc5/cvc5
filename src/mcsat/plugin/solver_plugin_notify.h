#pragma once

#include <set>
#include <vector>

#include "mcsat/variable/variable.h"
#include "mcsat/clause/clause_ref.h"

namespace CVC4 {
namespace mcsat {

class SolverPlugin;
  
/** 
 * Kinds of notification a solver can get
 */
enum NotificationType {
  /** Nofity of a new assertion */
  NOTIFY_ASSERTION,
  /** Notify of a restart */
  NOTIFY_RESTART,
  /** Notify of a conflict */
  NOTIFY_CONFLICT,
  /** Notify of a conflict resolution step */
  NOTIFY_CONFLICT_RESOLUTION,
  /** Notify of backjump and unset of variabels */
  NOTIFY_BACKJUMP,
};

/**
 * Interface for plugin notification.
 */
class SolverPluginNotify {

public:
  
  typedef std::set<NotificationType> notification_set;

private:
  
  /** Which notifications the plugin asks for */
  notification_set d_notifications;
  
protected:
  
  /** To be called by plugins to subscribe */
  void addNotification(NotificationType type) {
    d_notifications.insert(type);
  }

public:
  
  virtual ~SolverPluginNotify() {}

  /** Get all notification types */
  const notification_set& getNotificationTypes() const {
    return d_notifications;
  }

  /** Nofification of a new assertion */
  virtual void notifyAssertion(TNode assertion) {
    Unreachable("If you subscribe, then reimplement");
  }
  
  /** Notification of a restart */
  virtual void notifyRestart() {
    Unreachable("If you subscribe, then reimplement");
  }

  /** Notification of a new conflict */
  virtual void notifyConflict() {
    Unreachable("If you subscribe, then reimplement");
  }

  /** Nofification of a new conflict resolution step */
  virtual void notifyConflictResolution(CRef clause) {
    Unreachable("If you subscribe, then reimplement");
  }
  
  /** Notification of a backjump */
  virtual void notifyBackjump(const std::vector<Variable>& unsetVariables) {
    Unreachable("If you subscribe, then reimplement");
  }

};


/**
 * Class to collect plugins and notify them.
 */
class NotificationDispatch : public SolverPluginNotify  {

  /** All plugins arranged by notifications */
  std::vector< std::vector<SolverPlugin*> > d_toNotify;

public:
  
  /** Add a plugin to notify */
  void addPlugin(SolverPlugin* plugin);
  
  /** Nofification of a new assertion */
  void notifyAssertion(TNode assertion);
  
  /** Notification of a new conflict */
  void notifyRestart();

  /** Notification of a new conflict */
  void notifyConflict();
  
  /** Nofification of a new conflict resolution step */
  void notifyConflictResolution(CRef clause);
  
  /** Notification of a backjump */
  void notifyBackjump(const std::vector<Variable>& unsetVars);
};

}
}
