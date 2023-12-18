-------------------------------- MODULE Saw --------------------------------

EXTENDS Integers, Sequences, TLC

(* --algorithm Saw

variables
  power          = TRUE,  (* кнопка питания *)
  standby        = FALSE, (* режим ожидания *)
  saw_run        = FALSE, (* пильный диск вращается *)
  bypass         = FALSE, (* включен режим Bypass *)
  start          = FALSE, (* кнопка управления работой пилы *)
  disk_size      = FALSE, (* установлен диск неподходящего размера *)
  stop_disk      = FALSE, (* лезвие застопорилось *)
  contact        = FALSE, (* тормозной картридж активирован *)

define
Safety_PowerButton == [] (power = TRUE) => (standby = TRUE \/ disk_size = TRUE \/ power = TRUE)
Safety_DiskSize == [] (disk_size = TRUE) => (power = TRUE)
Safety_BypassMode == [] (bypass = TRUE) => (contact = FALSE)
Safety_BrakeActivation == [] (contact = TRUE) => (power = TRUE)

Liveness_SawRunning == [] (saw_run = TRUE /\ start = TRUE) => (saw_run = TRUE)
Liveness_PowerAfterDiskSize == [] (disk_size = TRUE) => (power = TRUE)

end define;

process PowerControl = 1
begin
PowerControl:
  while TRUE do
    if (power = TRUE) then
      either
        power     := FALSE;
        disk_size := TRUE;
      or
        power   := FALSE;
        standby := TRUE;
      end either;
    else
      skip;
    end if;
  end while;
end process;

process DiskSizeControl = 2
begin
DiskSizeControl:
  while TRUE do
    if (disk_size = TRUE) then
      disk_size := FALSE;
      power     := TRUE;
    else
      skip;
    end if;
  end while;
end process;

process StandbyControl = 3
begin
StandbyControl:
  while TRUE do
    if (standby = TRUE /\ bypass = FALSE) then
      either
        standby := FALSE;
        power   := TRUE;
      or
        bypass := TRUE;
      or
        standby := FALSE;
        saw_run := TRUE;
        start   := TRUE;
      end either;
    else
      skip;
    end if;
  end while;
end process;

process StandbyBypassControl = 4
begin
StandbyBypassControl:
  while TRUE do
    if (standby = TRUE /\ bypass = TRUE) then
      either
        bypass := FALSE;
      or
        standby := FALSE;
        saw_run := TRUE;
        start   := TRUE;
      end either;
    else
      skip;
    end if;
  end while;
end process;

process SawControl = 6
begin
SawControl:
  while TRUE do
    if (saw_run = TRUE /\ start = TRUE) then
      either
        saw_run   := FALSE;
        stop_disk := TRUE;
      or
        saw_run := FALSE;
        start   := FALSE;
        standby := TRUE;
      or
        if(bypass = FALSE) then
          saw_run := FALSE;
          contact := TRUE;
        end if;
      end either;
    else
      skip;
    end if;
  end while;
end process;

process StopDiskControl = 7
begin
StopDiskControl:
  while TRUE do
    if (start = TRUE /\ stop_disk = TRUE) then
        stop_disk := FALSE;
        start     := FALSE;
        standby   := TRUE;
    else
      skip;
    end if;
  end while;
end process;

process ContactControl = 7
begin
ContactControl:
  while TRUE do
    if (start = TRUE /\ contact = TRUE) then
        contact := FALSE;
        start   := FALSE;
        power   := TRUE;
    end if;
  end while;
end process;

end algorithm 


*)
\* BEGIN TRANSLATION (chksum(pcal) = "efb8bb37" /\ chksum(tla) = "ef278978")
\* Label PowerControl of process PowerControl at line 31 col 3 changed to PowerControl_
\* Label DiskSizeControl of process DiskSizeControl at line 49 col 3 changed to DiskSizeControl_
\* Label StandbyControl of process StandbyControl at line 62 col 3 changed to StandbyControl_
\* Label StandbyBypassControl of process StandbyBypassControl at line 83 col 3 changed to StandbyBypassControl_
\* Label SawControl of process SawControl at line 101 col 3 changed to SawControl_
\* Label StopDiskControl of process StopDiskControl at line 125 col 3 changed to StopDiskControl_
\* Label ContactControl of process ContactControl at line 139 col 3 changed to ContactControl_
VARIABLES power, standby, saw_run, bypass, start, disk_size, stop_disk, 
          contact

(* define statement *)
Safety_PowerButton == [] (power = TRUE) => (standby = TRUE \/ disk_size = TRUE \/ power = TRUE)
Safety_DiskSize == [] (disk_size = TRUE) => (power = TRUE)
Safety_BypassMode == [] (bypass = TRUE) => (contact = FALSE)
Safety_BrakeActivation == [] (contact = TRUE) => (power = TRUE)

Liveness_SawRunning == [] (saw_run = TRUE /\ start = TRUE) => (saw_run = TRUE)
Liveness_PowerAfterDiskSize == [] (disk_size = TRUE) => (power = TRUE)


vars == << power, standby, saw_run, bypass, start, disk_size, stop_disk, 
           contact >>

ProcSet == {1} \cup {2} \cup {3} \cup {4} \cup {6} \cup {7} \cup {7}

Init == (* Global variables *)
        /\ power = TRUE
        /\ standby = FALSE
        /\ saw_run = FALSE
        /\ bypass = FALSE
        /\ start = FALSE
        /\ disk_size = FALSE
        /\ stop_disk = FALSE
        /\ contact = FALSE

PowerControl == /\ IF (power = TRUE)
                      THEN /\ \/ /\ power' = FALSE
                                 /\ disk_size' = TRUE
                                 /\ UNCHANGED standby
                              \/ /\ power' = FALSE
                                 /\ standby' = TRUE
                                 /\ UNCHANGED disk_size
                      ELSE /\ TRUE
                           /\ UNCHANGED << power, standby, disk_size >>
                /\ UNCHANGED << saw_run, bypass, start, stop_disk, contact >>

DiskSizeControl == /\ IF (disk_size = TRUE)
                         THEN /\ disk_size' = FALSE
                              /\ power' = TRUE
                         ELSE /\ TRUE
                              /\ UNCHANGED << power, disk_size >>
                   /\ UNCHANGED << standby, saw_run, bypass, start, stop_disk, 
                                   contact >>

StandbyControl == /\ IF (standby = TRUE /\ bypass = FALSE)
                        THEN /\ \/ /\ standby' = FALSE
                                   /\ power' = TRUE
                                   /\ UNCHANGED <<saw_run, bypass, start>>
                                \/ /\ bypass' = TRUE
                                   /\ UNCHANGED <<power, standby, saw_run, start>>
                                \/ /\ standby' = FALSE
                                   /\ saw_run' = TRUE
                                   /\ start' = TRUE
                                   /\ UNCHANGED <<power, bypass>>
                        ELSE /\ TRUE
                             /\ UNCHANGED << power, standby, saw_run, bypass, 
                                             start >>
                  /\ UNCHANGED << disk_size, stop_disk, contact >>

StandbyBypassControl == /\ IF (standby = TRUE /\ bypass = TRUE)
                              THEN /\ \/ /\ bypass' = FALSE
                                         /\ UNCHANGED <<standby, saw_run, start>>
                                      \/ /\ standby' = FALSE
                                         /\ saw_run' = TRUE
                                         /\ start' = TRUE
                                         /\ UNCHANGED bypass
                              ELSE /\ TRUE
                                   /\ UNCHANGED << standby, saw_run, bypass, 
                                                   start >>
                        /\ UNCHANGED << power, disk_size, stop_disk, contact >>

SawControl == /\ IF (saw_run = TRUE /\ start = TRUE)
                    THEN /\ \/ /\ saw_run' = FALSE
                               /\ stop_disk' = TRUE
                               /\ UNCHANGED <<standby, start, contact>>
                            \/ /\ saw_run' = FALSE
                               /\ start' = FALSE
                               /\ standby' = TRUE
                               /\ UNCHANGED <<stop_disk, contact>>
                            \/ /\ IF (bypass = FALSE)
                                     THEN /\ saw_run' = FALSE
                                          /\ contact' = TRUE
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << saw_run, contact >>
                               /\ UNCHANGED <<standby, start, stop_disk>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << standby, saw_run, start, stop_disk, 
                                         contact >>
              /\ UNCHANGED << power, bypass, disk_size >>

StopDiskControl == /\ IF (start = TRUE /\ stop_disk = TRUE)
                         THEN /\ stop_disk' = FALSE
                              /\ start' = FALSE
                              /\ standby' = TRUE
                         ELSE /\ TRUE
                              /\ UNCHANGED << standby, start, stop_disk >>
                   /\ UNCHANGED << power, saw_run, bypass, disk_size, contact >>

ContactControl == /\ IF (start = TRUE /\ contact = TRUE)
                        THEN /\ contact' = FALSE
                             /\ start' = FALSE
                             /\ power' = TRUE
                        ELSE /\ TRUE
                             /\ UNCHANGED << power, start, contact >>
                  /\ UNCHANGED << standby, saw_run, bypass, disk_size, 
                                  stop_disk >>

Next == PowerControl \/ DiskSizeControl \/ StandbyControl
           \/ StandbyBypassControl \/ SawControl \/ StopDiskControl
           \/ ContactControl

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Mon Dec 18 21:41:01 MSK 2023 by anton
\* Created Sat Dec 02 14:08:43 MSK 2023 by anton
